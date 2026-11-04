module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Deformation.ToposThickening.ExtensionFunctoriality
public import StacksFrontier.Deformation.ToposThickening.FinitePresentationAcrossThickening

/-!
# Lifting a local presentation of the reduction across a first order thickening

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi with square-zero
ideal `I = Ker(i^♯) ⊂ O'`, let `ℱ'` be a sheaf of `O'`-modules and write `ℱ = i^*ℱ'` for its
reduction.

In the proof of the direction (2) ⇒ (1) of Stacks 08VU the source picks, over an object `V` of
the thickened site, a finite presentation of the reduction and lifts it: it lifts the `n`
generating sections of `ℱ` to sections of `ℱ'`, lifts the `m` relation tuples through
`O' ⟶ i_*O`, and then *corrects* the lifted relations, which are relations only modulo `I`, into
relations on the nose. This file carries those three steps, and the packaging of section-level
presentation data into `SheafOfModules.IsFinitePresentation`.

Every statement here is unconditional: no flatness of `ℱ'` over a thickened base and no
strictness of a square of thickenings is used, and the hypotheses of Stacks 08MQ are nowhere
appealed to.

## Main results

* `Stacks.SheafOfModules.LocalLift.exists_cover_lift_finite_sections`: **finitely many sections
  lift simultaneously.** A finite family of sections of the target of a locally surjective
  morphism of presheaves lifts after restriction along the arrows of one covering sieve — the
  infimum of the finitely many image sieves. Its two instances here are the unit
  `ℱ' ⟶ i_*i^*ℱ'`, which is an epimorphism, and the structure map `O' ⟶ i_*O`, which is
  locally surjective by definition of a thickening:
  `Deformation.ToposThickening.exists_cover_lift_unit_sections` is **step (1)**, the lifting of
  the generators, and `Deformation.ToposThickening.exists_cover_lift_structure_sections` is
  **step (2)**, the lifting of the relations.
* `Deformation.ToposThickening.kerSpanSieve_mem_of_mem_idealProductSubmodule`: **a section of
  the ideal product is locally a combination of the lifted generators with coefficients in the
  ideal.** This is the mechanism of the correction: a tuple of sections of `O'` whose
  combination dies in the reduction can be altered by sections of `I`, which changes nothing in
  the reduction, so as to kill the combination outright.
* `Deformation.ToposThickening.exists_cover_corrected_relations`: **step (3)**, the correction
  itself.
* `Deformation.ToposThickening.locallySpans_of_locallySpansModIdealProduct`: **generators
  modulo the ideal product generate.** The Nakayama step: `I·(I·ℱ') = 0`, so a family of
  sections generating `ℱ'` modulo `I·ℱ'` generates `ℱ'`.
* `Deformation.ToposThickening.exists_cover_corrected_relations_and_locallySpans`: steps (1)–(3)
  assembled — after refining the covering, the lifted data satisfies the conditions (A) and (B)
  of `Stacks.Sheaves.LocalGeneration.IsPresentationData`.
* `Stacks.SheafOfModules.isFinitePresentation_of_locally_isPresentationData`: **the
  packaging.** Section-level presentation data over the members of a covering of each object of
  the site makes a sheaf of modules of finite presentation.

## How the correction works

Fix `n` sections `s` of `ℱ'` over `V`. The whole argument turns on one sheaf submodule of `ℱ'`,
`idealKerSpanSubmodule`: the sections every restriction of which, over an object above `V`, is
locally a combination of the `s j` with all coefficients killed by `i^♯`. The quantification
over objects above `V` is what makes this a submodule of `ℱ'` itself and not of its restriction
to the slice site at `V`, so that the universal property of `I·ℱ'` — being the *smallest* sheaf
submodule containing every product of a section of `I` with a section of `ℱ'` — can be applied
to it.

That the submodule contains those products is the only computation: a section `m` of `ℱ'` is
locally `∑ c_j s_j + z` with `z` a section of `I·ℱ'`, so for a section `a` of `I`,

```
  a · m = ∑ (a c_j) s_j + a · z = ∑ (a c_j) s_j,
```

the last term vanishing because `I` annihilates `I·ℱ'`
(`Deformation.ToposThickening.FirstOrderThickening.smul_mem_idealProductSubmodule_eq_zero`),
and the coefficients `a c_j` are killed by `i^♯`. Hence `I·ℱ'` is contained in the submodule,
which is to say that a section dying in the reduction is locally an `I`-combination of the
`s j`. Both remaining steps are immediate from this: subtracting such a combination from a
lifted relation makes it a relation, and adding one to a combination representing a section
modulo `I·ℱ'` makes it represent the section.

A section dies in the reduction exactly when it lies in `I·ℱ'`, which is
`Deformation.ToposThickening.mem_idealProductSubmodule_of_unit_eq_zero`: the ideal-product
sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i_*i^*ℱ' ⟶ 0` is short exact
(`Deformation.ToposThickening.idealProductShortComplex_shortExact`), so the inclusion of
`I·ℱ'` is a kernel of the unit, and a kernel of a morphism of sheaves of modules is computed on
sections.

## Implementation notes

**Nothing is formed on a slice site except by the packaging lemma.** Conditions (A), (B) and
(C) of `Stacks.Sheaves.LocalGeneration.IsPresentationData` are statements about sections of
`ℱ'` and of `O'` over objects of the thickened site, and `Stacks.SheafOfModules`'s decoding of
that data into a `SheafOfModules.Presentation` of `ℱ'|_V` forms no cokernel diagram and needs
no exactness statement. This is what lets the three steps be carried out with the thickening
only in its global form.

**The structure map is read twice.** `Deformation.ToposThickening.structureRingMap` is `i^♯`
composed with the forgetful functor `CommRingCat ⥤ RingCat`, so that it is a morphism of the
*underlying sheaves of rings*, the spelling in which a section of `O'` presented as a section of
`ringSheaf Y.O` can be fed to `map_add`, `map_mul` and naturality. The `CommRingCat` spelling
`i.fSharp.hom.app U` accepts the same sections — the carrier types are definitionally equal — but
its `RingHom` structure is not found by instance search at that spelling.

**`i` is an explicit argument of `kerSpanSieve` and of `idealKerSpanSubmodule`.** It occurs in
neither's ascribed type, only inside the predicate they define, so it cannot be inferred.

## Scope

What this file supplies of the direction (2) ⇒ (1) of Stacks 08VU is the lifting of the
generators and relations and the correction of the relations, i.e. the conditions (A) and (B) of
`Stacks.Sheaves.LocalGeneration.IsPresentationData` for the lifted data, together with the
packaging of complete data into `SheafOfModules.IsFinitePresentation`. The condition (C) — that
*every* relation among the lifted generators is locally a combination of the corrected relations
— is the step where the source uses its hypotheses, and it is proved, with the tag itself, in
`StacksFrontier/Deformation/ToposThickening/FinitePresentationFlatLift.lean`.

## References

* [Stacks Project, Tag 08VU](https://stacks.math.columbia.edu/tag/08VU)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)
open Stacks.Sheaves.LocalGeneration

namespace Stacks.SheafOfModules.LocalLift

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **A finite family of sections lifts locally along a locally surjective morphism of
presheaves.** Each individual section lifts on a covering sieve, and the infimum of finitely
many covering sieves is covering. -/
theorem exists_cover_lift_finite_sections {A : Type*} [Category A] {FA : A → A → Type*}
    {CA : A → Type*} [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory A FA]
    {F G : Cᵒᵖ ⥤ A} (φ : F ⟶ G) [Presheaf.IsLocallySurjective J φ] {U : C}
    {ι : Type*} [Fintype ι] (y : ι → ToType (G.obj (op U))) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), S g →
      ∃ x : ι → ToType (F.obj (op V)), ∀ j, φ.app (op V) (x j) = G.map g.op (y j) := by
  classical
  refine ⟨⨅ j, Presheaf.imageSieve φ (y j),
    Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem J _ fun j =>
      Presheaf.imageSieve_mem J φ (y j),
    fun V g hg => ?_⟩
  have h : ∀ j, Presheaf.imageSieve φ (y j) g :=
    (Stacks.SheafOfModules.FiniteTypeKernel.iInf_apply _ g).mp hg
  exact ⟨fun j => (h j).choose, fun j => (h j).choose_spec⟩

section Restriction

variable {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)

/-- Restriction of sections of a sheaf of modules is additive. -/
lemma restr_add {U V : Cᵒᵖ} (g : U ⟶ V) (x y : M.val.obj U) :
    restr M g (x + y) = restr M g x + restr M g y :=
  map_add (M.val.map g).hom x y

/-- Restriction of sections of a sheaf of modules carries differences to differences. -/
lemma restr_sub {U V : Cᵒᵖ} (g : U ⟶ V) (x y : M.val.obj U) :
    restr M g (x - y) = restr M g x - restr M g y :=
  map_sub (M.val.map g).hom x y

/-- A linear combination is additive in its coefficients. -/
lemma combinationValue_add {U : Cᵒᵖ} {r : ℕ} (a b : Fin r → R.obj.obj U)
    (s : Fin r → M.val.obj U) :
    combinationValue M (fun j => a j + b j) s =
      combinationValue M a s + combinationValue M b s := by
  simp [combinationValue, add_smul, Finset.sum_add_distrib]

/-- A linear combination carries differences of coefficients to differences. -/
lemma combinationValue_sub {U : Cᵒᵖ} {r : ℕ} (a b : Fin r → R.obj.obj U)
    (s : Fin r → M.val.obj U) :
    combinationValue M (fun j => a j - b j) s =
      combinationValue M a s - combinationValue M b s := by
  simp [combinationValue, sub_smul, Finset.sum_sub_distrib]

/-- Restriction of sections of a sheaf of modules is semilinear. -/
lemma restr_smul {U V : Cᵒᵖ} (g : U ⟶ V) (r : R.obj.obj U) (x : M.val.obj U) :
    restr M g (r • x) = R.obj.map g r • restr M g x :=
  M.val.map_smul g r x

/-- A linear combination with vanishing coefficients vanishes. -/
lemma combinationValue_zero {U : Cᵒᵖ} {r : ℕ} (s : Fin r → M.val.obj U) :
    combinationValue M (fun _ => (0 : R.obj.obj U)) s = 0 := by
  simp [combinationValue]

/-- Scaling a linear combination scales its coefficients. -/
lemma smul_combinationValue {U : Cᵒᵖ} {r : ℕ} (c : R.obj.obj U) (a : Fin r → R.obj.obj U)
    (s : Fin r → M.val.obj U) :
    c • combinationValue M a s = combinationValue M (fun j => c * a j) s := by
  simp [combinationValue, Finset.smul_sum, smul_smul]

end Restriction

variable {R : Sheaf J RingCat.{w}} [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A finite family of sections of a sheaf of modules lifts locally along an epimorphism.**
An epimorphism of sheaves of modules is locally surjective on sections (Stacks 01AH, in the
form `Stacks.SheafOfModules.EpiMono.imageSieve_mem_of_epi`), and finitely many covering sieves
have a covering infimum. -/
theorem exists_cover_lift_finite_module_sections {M N : SheafOfModules.{w} R} (p : M ⟶ N)
    [Epi p] {U : C} {ι : Type*} [Fintype ι] (y : ι → N.val.obj (op U)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), S g →
      ∃ x : ι → M.val.obj (op V), ∀ j, p.val.app (op V) (x j) = restr N g.op (y j) := by
  have : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map p.val) :=
    ⟨fun s => Stacks.SheafOfModules.EpiMono.imageSieve_mem_of_epi p s⟩
  exact exists_cover_lift_finite_sections (J := J)
    ((PresheafOfModules.toPresheaf R.obj).map p.val) (U := U) y

/-- **A section killed by the right-hand map of a short exact sequence comes from the left-hand
term.** Evaluation at an object of the site preserves the kernel of the right-hand map, which
the left-hand map is; the section is then the image of the lift of the scalar `1`. -/
theorem exists_preimage_of_mem_kernel {S : ShortComplex (SheafOfModules.{w} R)}
    (hS : S.ShortExact) (U : Cᵒᵖ) (x : S.X₂.val.obj U) (hx : S.g.val.app U x = 0) :
    ∃ y : S.X₁.val.obj U, S.f.val.app U y = x := by
  have hf : IsLimit (KernelFork.ofι S.f S.zero) :=
    (S.exact_and_mono_f_iff_f_is_kernel.mp ⟨hS.exact, hS.mono_f⟩).some
  let ev := _root_.SheafOfModules.evaluation R U
  have hf' : IsLimit ((KernelFork.ofι S.f S.zero).map ev) :=
    KernelFork.isLimitMapConeEquiv (KernelFork.ofι S.f S.zero) ev (isLimitOfPreserves ev hf)
  let xmap : ModuleCat.of (R.obj.obj U) (R.obj.obj U) ⟶ ev.obj S.X₂ :=
    ModuleCat.ofHom (LinearMap.smulRight LinearMap.id x)
  have hx1 : xmap 1 = x := by
    change ((LinearMap.id : (R.obj.obj U) →ₗ[R.obj.obj U] (R.obj.obj U)) 1) • x = x
    simp
  have hxmap : xmap ≫ ev.map S.g = 0 := by
    ext
    rw [ModuleCat.comp_apply, hx1]
    exact hx
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hf' xmap hxmap
  refine ⟨l 1, ?_⟩
  simp only [KernelFork.map_ι, KernelFork.ι_ofι] at hl
  exact (congrArg (fun q => q 1) hl).trans hx1

end Stacks.SheafOfModules.LocalLift

namespace Deformation.ToposThickening

universe v u v' u' w

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

section ScalarKernel

variable {i : RingedToposHom X Y}

/-- A section of `O'` killed by the structure map is killed after restriction. -/
theorem structureRingMap_map_eq_zero {U V : Y.Cᵒᵖ} (f : U ⟶ V)
    {a : (ringSheaf Y.O).obj.obj U}
    (ha : (structureRingMap i).hom.app U a = 0) :
    (structureRingMap i).hom.app V ((ringSheaf Y.O).obj.map f a) = 0 := by
  rw [NatTrans.naturality_apply (structureRingMap i).hom f a, ha, map_zero]

/-- A left multiple of a section of `O'` killed by the structure map is killed by it. -/
theorem structureRingMap_mul_eq_zero {U : Y.Cᵒᵖ} (r : (ringSheaf Y.O).obj.obj U)
    {a : (ringSheaf Y.O).obj.obj U}
    (ha : (structureRingMap i).hom.app U a = 0) :
    (structureRingMap i).hom.app U (r * a) = 0 := by
  rw [map_mul, ha, mul_zero]

/-- A right multiple of a section of `O'` killed by the structure map is killed by it. -/
theorem structureRingMap_mul_eq_zero' {U : Y.Cᵒᵖ} (r : (ringSheaf Y.O).obj.obj U)
    {a : (ringSheaf Y.O).obj.obj U}
    (ha : (structureRingMap i).hom.app U a = 0) :
    (structureRingMap i).hom.app U (a * r) = 0 := by
  rw [map_mul, ha, zero_mul]

/-- The inclusion of the square-zero ideal lands in the kernel of the structure map. -/
theorem structureRingMap_incl_eq_zero (hi : FirstOrderThickening i) {U : Y.Cᵒᵖ}
    (b : hi.I.val.obj U) :
    (structureRingMap i).hom.app U
      (show (ringSheaf Y.O).obj.obj U from hi.incl.val.app U b) = 0 :=
  (hi.kernel U _).2 ⟨b, rfl⟩

end ScalarKernel

/-- **The sieve on which a section becomes a combination of `s` with ideal coefficients.** For a
finite family `s` of sections of `ℱ'` over `V` and a section `y` of `ℱ'` over an object `W`
above `V`, this is the sieve of arrows along which `y` becomes a linear combination of the
restrictions of the `s j` all of whose coefficients are killed by the structure map. -/
@[simps]
noncomputable def kerSpanSieve (i : RingedToposHom X Y)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {V W : Y.C} (h : W ⟶ V) {n : ℕ} (s : Fin n → F'.val.obj (op V))
    (y : F'.val.obj (op W)) : Sieve W where
  arrows W' k := ∃ c : Fin n → (ringSheaf Y.O).obj.obj (op W'),
    (∀ j, (structureRingMap i).hom.app (op W') (c j) = 0) ∧
      combinationValue F' c (fun j => restr F' (k ≫ h).op (s j)) = restr F' k.op y
  downward_closed := by
    rintro W' W'' k ⟨c, hc, heq⟩ l
    refine ⟨fun j => (ringSheaf Y.O).obj.map l.op (c j),
      fun j => structureRingMap_map_eq_zero l.op (hc j), ?_⟩
    have hr := congrArg (restr F' l.op) heq
    rw [restr_combinationValue] at hr
    simpa only [restr_restr, ← op_comp, Category.assoc] using hr

open Stacks.SheafOfModules.LocalLift in
/-- **The sheaf submodule of sections that are locally ideal combinations of `s`.** A section `y`
of `ℱ'` over `W` belongs to it when, for every object `W'` above both `W` and `V`, the
restriction of `y` to `W'` becomes on a covering of `W'` a linear combination of the
restrictions of the `s j` all of whose coefficients are killed by the structure map.

The quantification over objects above `V` is what makes this a submodule of `ℱ'` itself rather
than of its restriction to the slice site at `V`: the family `s` is a family of sections over
`V`, so there is nothing to say about a section over an object admitting no map to `V`, and the
condition is vacuous there. -/
private noncomputable def idealKerSpanSubmodule (i : RingedToposHom X Y)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {V : Y.C} {n : ℕ} (s : Fin n → F'.val.obj (op V)) : F'.Submodule := by
  refine ⟨{
    obj := fun W =>
      { carrier := {y | ∀ (W' : Y.C) (g : W' ⟶ W.unop) (h : W' ⟶ V),
          kerSpanSieve i F' h s (restr F' g.op y) ∈ Y.J W'}
        add_mem' := ?_
        zero_mem' := ?_
        smul_mem' := ?_ }
    map := ?_ }, ?_⟩
  · intro y₁ y₂ h₁ h₂ W' g h
    refine Y.J.superset_covering ?_ (Y.J.intersection_covering (h₁ W' g h) (h₂ W' g h))
    rintro W'' k ⟨⟨c₁, hc₁, he₁⟩, ⟨c₂, hc₂, he₂⟩⟩
    refine ⟨fun j => c₁ j + c₂ j, fun j => by rw [map_add, hc₁ j, hc₂ j, add_zero], ?_⟩
    rw [combinationValue_add, he₁, he₂, restr_add, restr_add]
  · intro W' g h
    refine Y.J.superset_covering ?_ (Y.J.top_mem W')
    intro W'' k _
    refine ⟨fun _ => 0, fun _ => map_zero _, ?_⟩
    rw [combinationValue_zero, restr_zero, restr_zero]
  · intro r y hy W' g h
    refine Y.J.superset_covering ?_ (hy W' g h)
    rintro W'' k ⟨c, hc, he⟩
    refine ⟨fun j => (ringSheaf Y.O).obj.map k.op
        ((ringSheaf Y.O).obj.map g.op r) * c j,
      fun j => structureRingMap_mul_eq_zero _ (hc j), ?_⟩
    have hrw : restr F' k.op (restr F' g.op (r • y)) =
        ((ringSheaf Y.O).obj.map k.op
          ((ringSheaf Y.O).obj.map g.op r)) •
            restr F' k.op (restr F' g.op y) := by
      rw [restr_smul, restr_smul]
    rw [hrw, ← he, smul_combinationValue]
  · intro W₁ W₂ f y hy W' g h
    have hrw : restr F' g.op ((F'.val.restrictₛₗ f) y) = restr F' (g ≫ f.unop).op y := by
      rw [show ((F'.val.restrictₛₗ f) y) = restr F' f y from rfl, restr_restr, op_comp,
        Quiver.Hom.op_unop]
    rw [hrw]
    exact hy W' (g ≫ f.unop) h
  · intro W y hy W' g h
    apply Y.J.transitive (Y.J.pullback_stable g hy)
    intro W'' k hk
    have hmem : ∀ (Z : Y.C) (a : Z ⟶ W'') (b : Z ⟶ V),
        kerSpanSieve i F' b s (restr F' a.op (restr F' (k ≫ g).op y)) ∈ Y.J Z := hk
    refine Y.J.superset_covering ?_ (hmem W'' (𝟙 W'') (k ≫ h))
    rintro Z l ⟨c, hc, he⟩
    refine ⟨c, hc, ?_⟩
    simp only [op_id, restr_id] at he
    simpa only [restr_restr, ← op_comp, Category.assoc] using he

section Thickening

variable {i : RingedToposHom X Y}

/-- **The sieve on which a section becomes a combination of `s` modulo the ideal product.** For
a finite family `s` of sections of `ℱ'` over `V` and a section `y` of `ℱ'` over an object `W`
above `V`, this is the sieve of arrows along which `y` becomes a linear combination of the
restrictions of the `s j` up to a section of `I·ℱ'`. -/
@[simps]
noncomputable def modIdealSpanSieve (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {V W : Y.C} (h : W ⟶ V) {n : ℕ} (s : Fin n → F'.val.obj (op V))
    (y : F'.val.obj (op W)) : Sieve W where
  arrows W' k := ∃ c : Fin n → (ringSheaf Y.O).obj.obj (op W'),
    restr F' k.op y - combinationValue F' c (fun j => restr F' (k ≫ h).op (s j)) ∈
      (idealProductSubmodule hi F').obj (op W')
  downward_closed := by
    rintro W' W'' k ⟨c, hc⟩ l
    refine ⟨fun j => (ringSheaf Y.O).obj.map l.op (c j), ?_⟩
    have hmem : restr F' l.op (restr F' k.op y -
        combinationValue F' c (fun j => restr F' (k ≫ h).op (s j))) ∈
        (idealProductSubmodule hi F').obj (op W'') :=
      (idealProductSubmodule hi F').map_mem l.op hc
    rw [Stacks.SheafOfModules.LocalLift.restr_sub, restr_combinationValue] at hmem
    simpa only [restr_restr, ← op_comp, Category.assoc] using hmem

/-- **`s` spans `ℱ'` modulo the ideal product, locally.** Every section of `ℱ'` over an object
above `V` becomes, on a covering, a linear combination of the restrictions of the `s j` up to a
section of `I·ℱ'`.

For the lift `s` of a family of sections generating the reduction `ℱ = i^*ℱ'` this holds
unconditionally: the unit `ℱ' ⟶ i_*ℱ` is surjective with kernel `I·ℱ'`, and the structure map
`O' ⟶ i_*O` is locally surjective, so a coefficient of a combination in the reduction lifts
locally to a coefficient in `O'`. -/
def LocallySpansModIdealProduct (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {V : Y.C} {n : ℕ} (s : Fin n → F'.val.obj (op V)) : Prop :=
  ∀ (W : Y.C) (h : W ⟶ V) (y : F'.val.obj (op W)), modIdealSpanSieve hi F' h s y ∈ Y.J W

open Stacks.SheafOfModules.LocalLift in
/-- Restricting a product of a section of the ideal with a section of `ℱ'` restricts both
factors. -/
private theorem restr_incl_smul (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) {U V : Y.Cᵒᵖ} (f : U ⟶ V)
    (b : hi.I.val.obj U) (m : F'.val.obj U) :
    restr F' f
        ((show (ringSheaf Y.O).obj.obj U from hi.incl.val.app U b) • m) =
      (show (ringSheaf Y.O).obj.obj V from
        hi.incl.val.app V (hi.I.val.map f b)) • restr F' f m := by
  rw [restr, F'.val.map_smul]
  congr 1
  exact (PresheafOfModules.naturality_apply hi.incl.val f b).symm

open Stacks.SheafOfModules.LocalLift in
/-- **A product of a section of the ideal with a section of `ℱ'` is locally an ideal combination
of `s`.** This is the step where the square-zero condition enters: the section of `ℱ'` is
locally a combination of the `s j` up to a section of `I·ℱ'`, and the ideal annihilates `I·ℱ'`,
so the correction term disappears after multiplication. -/
private theorem smul_mem_idealKerSpanSubmodule (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {V : Y.C} {n : ℕ} (s : Fin n → F'.val.obj (op V))
    (hgen : LocallySpansModIdealProduct hi F' s)
    (W : Y.Cᵒᵖ) (b : hi.I.val.obj W) (m : F'.val.obj W) :
    (show (ringSheaf Y.O).obj.obj W from hi.incl.val.app W b) • m ∈
      (idealKerSpanSubmodule i F' s).obj W := by
  intro W' g h
  rw [restr_incl_smul hi F' g.op b m]
  refine Y.J.superset_covering ?_ (hgen W' h (restr F' g.op m))
  rintro W'' k ⟨c, hc⟩
  set a : (ringSheaf Y.O).obj.obj (op W'') :=
    hi.incl.val.app (op W'') (hi.I.val.map k.op (hi.I.val.map g.op b))
  have ha0 : (structureRingMap i).hom.app (op W'') a = 0 := structureRingMap_incl_eq_zero hi _
  refine ⟨fun j => a * c j, fun j => structureRingMap_mul_eq_zero' (c j) ha0, ?_⟩
  have hz := hi.smul_mem_idealProductSubmodule_eq_zero F' (op W'') a ha0 _ hc
  rw [smul_sub, sub_eq_zero] at hz
  rw [← smul_combinationValue, ← hz]
  exact (restr_incl_smul hi F' k.op (hi.I.val.map g.op b) (restr F' g.op m)).symm

/-- **The ideal product is contained in the submodule of local ideal combinations of `s`.**
By the universal property of `I·ℱ'` as the smallest sheaf submodule containing all products of
a section of the ideal with a section of `ℱ'`. -/
private theorem idealProductSubmodule_le_idealKerSpanSubmodule (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {V : Y.C} {n : ℕ} (s : Fin n → F'.val.obj (op V))
    (hgen : LocallySpansModIdealProduct hi F' s) :
    idealProductSubmodule hi F' ≤ idealKerSpanSubmodule i F' s :=
  sInf_le fun W b m => smul_mem_idealKerSpanSubmodule hi F' s hgen W b m

/-- **A section of the ideal product is locally a combination of `s` with ideal coefficients.**
This is the correction mechanism of the proof of Stacks 08VU (2) ⇒ (1): a section that dies in
the reduction is, after refining the covering, an `I`-linear combination of the lifted
generators, and subtracting it changes nothing in the reduction. -/
theorem kerSpanSieve_mem_of_mem_idealProductSubmodule (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {V : Y.C} {n : ℕ} (s : Fin n → F'.val.obj (op V))
    (hgen : LocallySpansModIdealProduct hi F' s) {W : Y.C} (h : W ⟶ V)
    (y : F'.val.obj (op W)) (hy : y ∈ (idealProductSubmodule hi F').obj (op W)) :
    kerSpanSieve i F' h s y ∈ Y.J W := by
  have hmem := idealProductSubmodule_le_idealKerSpanSubmodule hi F' s hgen (op W) hy
  simpa only [op_id, restr_id] using hmem W (𝟙 W) h

end Thickening

section Lifting

open Stacks.SheafOfModules.LocalLift

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X Y}

/-- **A section killed by the unit lies in the ideal product.** The ideal-product sequence
`0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i_*i^*ℱ' ⟶ 0` is short exact, so the inclusion of `I·ℱ'` is a kernel of the
unit, and a kernel of a morphism of sheaves of modules is computed on sections. -/
theorem mem_idealProductSubmodule_of_unit_eq_zero (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) (U : Y.Cᵒᵖ) (x : F'.val.obj U)
    (hx : (i.pullbackAdjPushforwardModulesViaComparison.unit.app F').val.app U x = 0) :
    x ∈ (idealProductSubmodule hi F').obj U := by
  let : HasSheafify Y.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  obtain ⟨y, rfl⟩ := exists_preimage_of_mem_kernel
    (idealProductShortComplex_shortExact hi F') U x hx
  exact y.property

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The lifted generators generate, not merely generate modulo the ideal product.** If every
section of `ℱ'` over an object above `V` is locally a combination of the `s j` up to a section
of `I·ℱ'`, then every section of `ℱ'` over an object above `V` is locally a combination of the
`s j` outright.

This is the Nakayama step of the proof of Stacks 08VU (2) ⇒ (1), and it uses none of the tag's
hypotheses: the correction term lies in `I·ℱ'`, which
`Deformation.ToposThickening.kerSpanSieve_mem_of_mem_idealProductSubmodule` rewrites locally as
a combination of the `s j` with coefficients in the ideal. -/
theorem locallySpans_of_locallySpansModIdealProduct (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {V : Y.C} {n : ℕ} (s : Fin n → F'.val.obj (op V))
    (hgen : LocallySpansModIdealProduct hi F' s) : LocallySpans F' s := by
  intro W g x
  apply Y.J.transitive (hgen W g x)
  rintro W'' k ⟨c, hc⟩
  refine Y.J.superset_covering ?_
    (kerSpanSieve_mem_of_mem_idealProductSubmodule hi F' s hgen (k ≫ g) _ hc)
  rintro Z l ⟨b, hb, he⟩
  refine ⟨fun j => (ringSheaf Y.O).obj.map l.op (c j) + b j, ?_⟩
  have h1 : combinationValue F' (fun j => (ringSheaf Y.O).obj.map l.op (c j))
      (fun j => restr F' (l ≫ k).op (restr F' g.op (s j))) =
      restr F' l.op (combinationValue F' c (fun j => restr F' (k ≫ g).op (s j))) := by
    rw [restr_combinationValue]
    simp only [restr_restr, ← op_comp, Category.assoc]
  have h2 : combinationValue F' b (fun j => restr F' (l ≫ k).op (restr F' g.op (s j))) =
      restr F' l.op (restr F' k.op x -
        combinationValue F' c (fun j => restr F' (k ≫ g).op (s j))) := by
    rw [← he]
    simp only [restr_restr, ← op_comp, Category.assoc]
  have h3 : restr F' l.op (restr F' k.op x) = restr F' (l ≫ k).op x := by
    rw [restr_restr, ← op_comp]
  rw [combinationValue_add, h1, h2, restr_sub, h3]
  abel

/-- **The corrected relations.** Suppose the `s j` generate `ℱ'` modulo the ideal product, and
suppose the `m` tuples `t k` of sections of `O'` become relations among the `s j` after passing
to the reduction. Then, after refining the covering, each `t k` can be corrected by a tuple of
sections of the square-zero ideal so as to become a relation among the `s j` on the nose; the
correction changes nothing in the reduction.

This is step (3) of the proof of the direction (2) ⇒ (1) of Stacks 08VU, and it uses none of the
tag's hypotheses. -/
theorem exists_cover_corrected_relations (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {V : Y.C} {n m : ℕ} (s : Fin n → F'.val.obj (op V))
    (t : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op V))
    (hgen : LocallySpansModIdealProduct hi F' s)
    (hrel : ∀ k, (i.pullbackAdjPushforwardModulesViaComparison.unit.app F').val.app (op V)
      (combinationValue F' (t k) s) = 0) :
    ∃ S : Sieve V, S ∈ Y.J V ∧ ∀ (W : Y.C) (g : W ⟶ V), S g →
      ∃ t' : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W),
        (∀ k j, (structureRingMap i).hom.app (op W) (t' k j) =
          (structureRingMap i).hom.app (op W)
            ((ringSheaf Y.O).obj.map g.op (t k j))) ∧
        (∀ k, combinationValue F' (t' k) (fun j => restr F' g.op (s j)) = 0) := by
  classical
  refine ⟨⨅ k, kerSpanSieve i F' (𝟙 V) s (combinationValue F' (t k) s),
    Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem Y.J _ fun k =>
      kerSpanSieve_mem_of_mem_idealProductSubmodule hi F' s hgen (𝟙 V) _
        (mem_idealProductSubmodule_of_unit_eq_zero hi F' (op V) _ (hrel k)), ?_⟩
  intro W g hg
  have hk : ∀ k, kerSpanSieve i F' (𝟙 V) s (combinationValue F' (t k) s) g :=
    (Stacks.SheafOfModules.FiniteTypeKernel.iInf_apply _ g).mp hg
  choose c hc0 hce using hk
  simp only [Category.comp_id] at hce
  refine ⟨fun k j => (ringSheaf Y.O).obj.map g.op (t k j) - c k j,
    fun k j => by rw [map_sub, hc0 k j, sub_zero], fun k => ?_⟩
  rw [combinationValue_sub, ← restr_combinationValue, hce k, sub_self]

/-- **Generation modulo the ideal product, read through the unit.** If every section of `ℱ'`
over an object above `V` becomes, on a covering, a combination of the `s j` after passing to the
reduction, then the `s j` generate `ℱ'` modulo the ideal product. This is the form in which the
hypothesis arises: the coefficients of a combination in the reduction are lifted along the
locally surjective structure map, and the resulting difference dies in the reduction. -/
theorem locallySpansModIdealProduct_of_unit (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {V : Y.C} {n : ℕ} (s : Fin n → F'.val.obj (op V))
    (h : ∀ (W : Y.C) (hW : W ⟶ V) (x : F'.val.obj (op W)),
      ∃ S : Sieve W, S ∈ Y.J W ∧ ∀ (W' : Y.C) (k : W' ⟶ W), S k →
        ∃ c : Fin n → (ringSheaf Y.O).obj.obj (op W'),
          (i.pullbackAdjPushforwardModulesViaComparison.unit.app F').val.app (op W')
            (restr F' k.op x -
              combinationValue F' c (fun j => restr F' (k ≫ hW).op (s j))) = 0) :
    LocallySpansModIdealProduct hi F' s := by
  intro W hW x
  obtain ⟨S, hS, hc⟩ := h W hW x
  refine Y.J.superset_covering ?_ hS
  intro W' k hk
  obtain ⟨c, hc'⟩ := hc W' k hk
  exact ⟨c, mem_idealProductSubmodule_of_unit_eq_zero hi F' (op W') _ hc'⟩

/-- **Step (1): the generators of the reduction lift after refining the covering.** The unit
`ℱ' ⟶ i_*i^*ℱ'` is an epimorphism (`epi_pullbackAdjPushforward_unit_app`), hence locally
surjective on sections, so finitely many sections of the reduction over `V` lift simultaneously
on a covering of `V`. -/
theorem exists_cover_lift_unit_sections (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) {V : Y.C} {ι : Type*} [Fintype ι]
    (y : ι → (i.pushforwardModules.obj
      (i.toRingedToposModulesHom.pullbackModules.obj F')).val.obj (op V)) :
    ∃ S : Sieve V, S ∈ Y.J V ∧ ∀ (W : Y.C) (g : W ⟶ V), S g →
      ∃ x : ι → F'.val.obj (op W), ∀ j,
        (i.pullbackAdjPushforwardModulesViaComparison.unit.app F').val.app (op W) (x j) =
          restr _ g.op (y j) := by
  let : HasSheafify Y.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have : Epi (i.pullbackAdjPushforwardModulesViaComparison.unit.app F') :=
    epi_pullbackAdjPushforward_unit_app hi F'
  exact exists_cover_lift_finite_module_sections
    (i.pullbackAdjPushforwardModulesViaComparison.unit.app F') y

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Step (2): the relations of the reduction lift through `O' ⟶ i_*O` after refining the
covering.** The structure map of a first order thickening is locally surjective, so finitely
many sections of `i_*O` over `V` lift simultaneously on a covering of `V`. -/
theorem exists_cover_lift_structure_sections (hi : FirstOrderThickening i) {V : Y.C}
    {ι : Type*} [Fintype ι]
    (a : ι → (ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj (op V)) :
    ∃ S : Sieve V, S ∈ Y.J V ∧ ∀ (W : Y.C) (g : W ⟶ V), S g →
      ∃ b : ι → (ringSheaf Y.O).obj.obj (op W), ∀ j,
        (structureRingMap i).hom.app (op W) (b j) =
          (ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.map g.op (a j) := by
  have : Presheaf.IsLocallySurjective Y.J i.fSharp.hom := hi.surjective
  have : Presheaf.IsLocallySurjective Y.J (structureRingMap i).hom :=
    ⟨fun s => Presheaf.imageSieve_mem Y.J i.fSharp.hom s⟩
  exact exists_cover_lift_finite_sections (J := Y.J) (structureRingMap i).hom a

/-- **The unconditional local lifting in the proof of the direction (2) ⇒ (1) of Stacks
08VU.** Let `ℱ'` be a sheaf of `O'`-modules, let `s` be `n` sections of `ℱ'` over `V` which
generate `ℱ'` modulo the ideal product `I·ℱ'`, and let `t` be `m` tuples of `n` sections of
`O'` over `V` which become relations among the `s j` in the reduction. Then, after refining the
covering of `V`, the `t k` can be corrected — by tuples of sections of the square-zero ideal, so
without changing anything in the reduction — into relations among the `s j` on the nose, and the
`s j` generate `ℱ'` outright.

These are the conditions (A) and (B) of `Stacks.Sheaves.LocalGeneration.IsPresentationData`,
and the argument uses none of the hypotheses of Stacks 08VU: neither flatness of `ℱ'` over the
thickened base nor strictness of the square. The condition (C) — that *every* relation among
the `s j` is locally a combination of the corrected `t k` — is the remaining step, and it is the
one that needs the tag's hypotheses. -/
theorem exists_cover_corrected_relations_and_locallySpans (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    {V : Y.C} {n m : ℕ} (s : Fin n → F'.val.obj (op V))
    (t : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op V))
    (hgen : LocallySpansModIdealProduct hi F' s)
    (hrel : ∀ k, (i.pullbackAdjPushforwardModulesViaComparison.unit.app F').val.app (op V)
      (combinationValue F' (t k) s) = 0) :
    ∃ S : Sieve V, S ∈ Y.J V ∧ ∀ (W : Y.C) (g : W ⟶ V), S g →
      ∃ t' : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W),
        (∀ k j, (structureRingMap i).hom.app (op W) (t' k j) =
          (structureRingMap i).hom.app (op W)
            ((ringSheaf Y.O).obj.map g.op (t k j))) ∧
        (∀ k, combinationValue F' (t' k) (fun j => restr F' g.op (s j)) = 0) ∧
        LocallySpans F' (U := W) (fun j => restr F' g.op (s j)) := by
  obtain ⟨S, hS, hc⟩ := exists_cover_corrected_relations hi F' s t hgen hrel
  refine ⟨S, hS, fun W g hg => ?_⟩
  obtain ⟨t', ht'0, ht'⟩ := hc W g hg
  exact ⟨t', ht'0, ht',
    locallySpans_map (locallySpans_of_locallySpansModIdealProduct hi F' s hgen) g⟩

end Lifting

end Deformation.ToposThickening


namespace Stacks.SheafOfModules

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Section-level presentation data, local on each object of the site, gives finite
presentation.** This is the packaging step: the data of `n` generating sections and `m` relation
tuples over the members of a covering of each object decodes, object by object, into a finite
`SheafOfModules.Presentation` of the restriction to the slice site
(`Stacks.SheafOfModules.exists_isFinite_presentation_over_of_isPresentationData`), and those
assemble into a `SheafOfModules.QuasicoherentData` with finite presentations
(`Stacks.SheafOfModules.isFinitePresentation_of_locally_presented`). No cokernel diagram and no
exactness statement is formed anywhere. -/
theorem isFinitePresentation_of_locally_isPresentationData (M : _root_.SheafOfModules.{w} R)
    (h : ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), S g →
      ∃ (n m : ℕ) (s : Fin n → M.val.obj (op V))
        (t : Fin m → Fin n → R.obj.obj (op V)), IsPresentationData M s t) :
    M.IsFinitePresentation := by
  let : ∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w} :=
    fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  refine isFinitePresentation_of_locally_presented M fun U => ?_
  obtain ⟨S, hS, hd⟩ := h U
  refine ⟨⟨S, hS⟩, fun V g hg => ?_⟩
  obtain ⟨n, m, s, t, hst⟩ := hd V g hg
  exact exists_isFinite_presentation_over_of_isPresentationData M s t hst

end Stacks.SheafOfModules

end
