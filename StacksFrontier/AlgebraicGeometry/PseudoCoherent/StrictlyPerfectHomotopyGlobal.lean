module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectHomotopy
public import StacksFrontier.AlgebraicGeometry.RingedSpace.RestrictTransitive
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local null homotopies for maps out of a strictly perfect complex

Let `X` be a ringed space and `α : ℰ ⟶ ℱ` a morphism of complexes of `𝒪_X`-modules with `ℰ`
strictly perfect, `ℰ^i = 0` for `i < a` and `H^i(ℱ) = 0` for `i ≥ a`. Then every point of `X`
has an open neighbourhood over which `α` is homotopic to zero (Stacks 08C7). This file supplies
the degreewise lifting and the family of maps satisfying the homotopy identity in every degree;
Stacks 08C7 itself is `AlgebraicGeometry.RingedSpace.exists_local_homotopy_zero_of_acyclic` and
`AlgebraicGeometry.RingedSpace.exists_local_homotopy_zero_of_isZero_homology`, which carry the
Tag 08C7 attribute.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_local_isNullHomotopyAt` builds, over a shrinking open
  subset, the family of maps satisfying the homotopy identity down to a given degree.
* `AlgebraicGeometry.RingedSpace.exists_local_lift_over_of_isDirectSummandOfFiniteFree` is the
  form of Stacks 08C6 the induction needs: the map to be lifted is defined only over an open
  subset, while the epimorphism it is lifted through is global.
* `AlgebraicGeometry.RingedSpace.exists_local_factorization_over` solves one of the degreewise
  lifting problems of the source proof over a smaller open subset.
* `CochainComplex.nonempty_homotopy_zero_of_isNullHomotopyAt` turns a family of maps satisfying
  the homotopy identity in every degree into a null homotopy.

## Implementation notes

Restriction to an open subset is taken in the slice idiom: `U ↦ SheafOfModules.overFunctor`,
whose target is the category of sheaves of modules over `R.over U` on the slice `Over U` of the
site of opens of `X`. The reason is that the lifting problems the source proof solves are
*sequential* — the map to be factored in degree `p` involves the homotopy already built in
degree `p + 1`, which exists only over the open subset produced at the previous step — so the
induction has to shrink the open subset at each of the `b - a + 1` steps. In the slice idiom all
the restrictions are indexed by one and the same lattice of opens of `X`, and
`SheafOfModules.overFunctorMap` identifies two successive restrictions with one; see
`StacksFrontier/AlgebraicGeometry/RingedSpace/RestrictTransitive.lean`. Restriction along an
inclusion of opens of `X` acts on morphisms between restrictions by
`SheafOfModules.overRestrict`.

The degreewise lifting problem is solved by Stacks 08C6, but in a form that
`AlgebraicGeometry.RingedSpace.exists_local_lift_of_isDirectSummandOfFiniteFree` does not have:
there the map to be lifted is a global morphism of `𝒪_X`-modules, whereas here it is only
defined over an open subset. The reduction to the finite free case and the passage from an
epimorphism to local surjectivity on sections are as in the source, the difference being that
the sections involved are sections over an open subset rather than global ones.

The map to be factored in degree `p` is killed by the differential, so it factors through the
cycles of `ℱ` in degree `p`; that this remains true after restriction is because restriction
preserves finite limits, hence carries the kernel fork exhibiting the cycles to a kernel fork.
From there the epimorphism `ℱ^{p-1} ⟶ Z^p(ℱ)` supplied by the vanishing of the cohomology
sheaf is global, which is what the relative form of 08C6 asks for.

The finite free module is written `⨁ (fun _ : Fin n => SheafOfModules.unit _)` rather than
`StrictlyPerfect.finiteFree X n`, which is the same object by definition, because the
identification of a morphism out of the unit sheaf of modules with a section
(`SheafOfModules.unitHomEquiv`) is stated for `SheafOfModules.unit`; a term of the other
spelling is converted once, where the retract data is named.

The other formulation of restriction in this development is
`AlgebraicGeometry.RingedSpace.restrictModules`, the pushforward to the ringed space
`X.restrict U.isOpenEmbedding` in which Stacks 08CB is phrased. The two are identified by
`TopologicalSpace.Opens.sheafOfModulesEquivOver`, Mathlib's equivalence
`SheafOfModules (R.over U) ≌ SheafOfModules (U.sheafRestrict.obj R)`, because
`structureSheafOfRings (X.restrict U.isOpenEmbedding)` *is*
`U.sheafRestrict.obj (structureSheafOfRings X)`.

Universes: the statement is at `AlgebraicGeometry.RingedSpace.{u, u}` with `𝒪_X`-modules in
universe `u`, which is the generality in which `StrictlyPerfect.OXMod` and
`StrictlyPerfect.IsStrictlyPerfect` are defined (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SheafLevel.lean`); the sheafification typeclasses
that give complexes of `𝒪_X`-modules cohomology are then found automatically.

## References

* [The Stacks Project, Lemma 20.46.5 (08C7)](https://stacks.math.columbia.edu/tag/08C7)
* [The Stacks Project, Lemma 20.46.4 (08C6)](https://stacks.math.columbia.edu/tag/08C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite TopologicalSpace
  StrictlyPerfect

open SheafOfModules (overFunctor overRestrict overUnitHom unitSection)

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

/-- Let `F` be an additive functor, `c` a finite family of objects and `γ` a morphism out of
`F (⨁ c)` to an arbitrary object of the target category. Assembling the composites of `γ` with
the images `F (ι j)` of the inclusions of the summands, through the exhibition of `F (⨁ c)` as
a retract of `⨁ F c` (`CategoryTheory.Functor.retractMapBiproduct`), recovers `γ`.

Indeed the composite is `∑ j, F (π j) ≫ F (ι j) ≫ γ = F (∑ j, π j ≫ ι j) ≫ γ`, and
`∑ j, π j ≫ ι j` is the identity. This generalizes
`CategoryTheory.Functor.retractMapBiproduct_i_desc`, whose target is the image of an object of
the source category; the generalization is what a map defined only after restriction needs. -/
public theorem retractMapBiproduct_i_desc_of_hom {J : Type} [Fintype J] (F : C ⥤ D) [F.Additive]
    (c : J → C) [HasBiproduct c] [HasBiproduct (F.obj ∘ c)] {Z : D} (γ : F.obj (⨁ c) ⟶ Z) :
    (F.retractMapBiproduct c).i ≫
      biproduct.desc (fun j => F.map (biproduct.ι c j) ≫ γ) = γ := by
  show F.biproductComparison c ≫ biproduct.desc (fun j => F.map (biproduct.ι c j) ≫ γ) = γ
  rw [CategoryTheory.Functor.biproductComparison, biproduct.lift_desc,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
      (Category.assoc (F.map (biproduct.π c j)) (F.map (biproduct.ι c j)) γ).symm,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
      congrArg (· ≫ γ) (F.map_comp (biproduct.π c j) (biproduct.ι c j)).symm,
    ← Preadditive.sum_comp, ← CategoryTheory.Functor.map_sum, biproduct.total,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The form in which `CategoryTheory.Functor.retractMapBiproduct_i_desc_of_hom` is used: if
each composite `F (ι j) ≫ γ` has been lifted through `p` to a map `b j`, then the map assembled
from the `b j` is a lift of `γ` through `p`. -/
public theorem retractMapBiproduct_i_desc_of_hom_comp {J : Type} [Fintype J] (F : C ⥤ D)
    [F.Additive] (c : J → C) [HasBiproduct c] [HasBiproduct (F.obj ∘ c)] {Y Z : D}
    (γ : F.obj (⨁ c) ⟶ Z) (p : Y ⟶ Z) (b : ∀ j, (F.obj ∘ c) j ⟶ Y)
    (hb : ∀ j, b j ≫ p = F.map (biproduct.ι c j) ≫ γ) :
    ((F.retractMapBiproduct c).i ≫ biproduct.desc b) ≫ p = γ :=
  calc ((F.retractMapBiproduct c).i ≫ biproduct.desc b) ≫ p
      = (F.retractMapBiproduct c).i ≫ (biproduct.desc b ≫ p) := Category.assoc _ _ _
    _ = (F.retractMapBiproduct c).i ≫
          biproduct.desc fun j => F.map (biproduct.ι c j) ≫ γ := by
        refine congrArg _ (biproduct.hom_ext' _ _ fun j => ?_)
        rw [← Category.assoc, biproduct.ι_desc, biproduct.ι_desc, hb j]
    _ = γ := F.retractMapBiproduct_i_desc_of_hom c γ

end CategoryTheory.Functor

namespace CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {E F : CochainComplex C ℤ}

/-- A family `h` of maps `E.X p ⟶ F.X q`, indexed by the pairs of integers with `q + 1 = p`,
which satisfies the homotopy identity between `α : E ⟶ F` and the zero map in every degree is a
null homotopy of `α`.

This is the final step of `CochainComplex.nonempty_homotopy_zero_of_exists_lift`, stated
separately: the induction building the family is different when the maps are only defined after
restriction to a shrinking open subset of a ringed space, but the passage from the family to the
homotopy is the same.

The homotopy is produced through `CochainComplex.HomComplex.Cochain.equivHomotopy`, which
identifies a homotopy from `α` to `0` with a `(-1)`-cochain `z` satisfying
`Cochain.ofHom α = δ (-1) 0 z`; the value of `δ (-1) 0 z` in degree `p` is exactly the
right-hand side of `CochainComplex.IsNullHomotopyAt`. -/
public theorem nonempty_homotopy_zero_of_isNullHomotopyAt (α : E ⟶ F)
    (h : ∀ p q : ℤ, q + 1 = p → (E.X p ⟶ F.X q)) (hall : ∀ p : ℤ, IsNullHomotopyAt α h p) :
    Nonempty (Homotopy α 0) := by
  refine ⟨(HomComplex.Cochain.equivHomotopy α 0).symm
    ⟨HomComplex.Cochain.mk fun p q hpq => h p q (by omega), ?_⟩⟩
  rw [HomComplex.Cochain.ofHom_zero, add_zero]
  ext p
  rw [HomComplex.Cochain.ofHom_v,
    HomComplex.δ_v (-1) 0 (by omega) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only [HomComplex.Cochain.mk_v, Int.negOnePow_zero, one_smul]
  exact hall p (p - 1) (p + 1) (by omega) rfl

end CochainComplex

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}}

/-- Restriction to an open subset `W` of a complex of `𝒪_X`-modules, and of a morphism of such
complexes, applied degreewise in the slice idiom. -/
public abbrev restrictComplexOver (X : RingedSpace.{u, u}) (W : Opens X.carrier) :
    CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ ⥤
      CochainComplex (SheafOfModules.{u} ((structureSheafOfRings X).over W)) ℤ :=
  (overFunctor (structureSheafOfRings X) W).mapHomologicalComplex (ComplexShape.up ℤ)

/-- An epimorphism `p : 𝒢 ⟶ ℱ` of `𝒪_X`-modules is locally surjective on sections over an open
subset: a section of `ℱ` over `W` is, on some smaller open neighbourhood of any given point of
`W`, the image of a section of `𝒢`.

This is the form of the sheaf-theoretic surjectivity of Stacks 007S the relative lifting lemma
needs; `AlgebraicGeometry.RingedSpace.exists_local_section_of_epi` is the special case of a
global section, together with the resulting neighbourhood not being required to lie in `W`. -/
public theorem exists_local_section_of_epi_mem {F G : StrictlyPerfect.OXMod.{u, u} X} (p : G ⟶ F)
    [Epi p] (W : Opens X.carrier) (σ : F.val.obj (op W)) {x : X.carrier} (hx : x ∈ W) :
    ∃ V : Opens X.carrier, ∃ hVW : V ≤ W, x ∈ V ∧ ∃ a : G.val.obj (op V),
      p.val.app (op V) a = F.val.map (homOfLE hVW).op σ := by
  have hp : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (structureSheafOfRings X)).map p).hom :=
    SheafOfModules.isLocallySurjective_toSheaf_of_epi p
  obtain ⟨V, hVW, ⟨a, ha⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp hp W σ x hx
  exact ⟨V, hVW, hxV, a, ha⟩

/-- Stacks 08C6 over an open subset, for the finite free module `𝒪_X^{⊕ n}`: a map
`q : 𝒪_X^{⊕ n}|_W ⟶ ℱ|_W` lifts through the restriction of a global epimorphism `p : 𝒢 ⟶ ℱ`
over a smaller open neighbourhood of any point of `W`.

The map `q` is the same data as its `n` components `𝒪_W ⟶ ℱ|_W`, that is, `n` sections of `ℱ`
over `W`; each is the image of a section of `𝒢` on some smaller neighbourhood of the given
point, and `W'` is the intersection of `W` with those finitely many neighbourhoods. -/
public theorem exists_local_lift_over_biproduct_unit
    {F G : StrictlyPerfect.OXMod.{u, u} X} (p : G ⟶ F) [Epi p] {n : ℕ} (W : Opens X.carrier)
    (q : (⨁ fun _ : Fin n => SheafOfModules.unit (structureSheafOfRings X)).over W ⟶ F.over W)
    {x : X.carrier} (hx : x ∈ W) :
    ∃ W' : Opens X.carrier, ∃ hW' : W' ≤ W, x ∈ W' ∧
      ∃ l : (⨁ fun _ : Fin n => SheafOfModules.unit (structureSheafOfRings X)).over W' ⟶
        G.over W', l ≫ (overFunctor (structureSheafOfRings X) W').map p =
          overRestrict (homOfLE hW') q := by
  classical
  choose V hVW hxV a ha using fun j : Fin n => exists_local_section_of_epi_mem p W
    (unitSection ((overFunctor (structureSheafOfRings X) W).map
      (biproduct.ι (fun _ : Fin n => SheafOfModules.unit (structureSheafOfRings X)) j) ≫ q)) hx
  refine ⟨W ⊓ ⨅ j, V j, inf_le_left, ⟨hx, ?_⟩, ?_⟩
  · rw [show ((⨅ j, V j : Opens X.carrier) : Set X.carrier) = _ from Opens.coe_iInf V,
      Set.mem_iInter]
    exact hxV
  have hle : ∀ j : Fin n, (W ⊓ ⨅ j, V j : Opens X.carrier) ≤ V j :=
    fun j => inf_le_right.trans (iInf_le V j)
  refine ⟨_, CategoryTheory.Functor.retractMapBiproduct_i_desc_of_hom_comp
    (overFunctor (structureSheafOfRings X) (W ⊓ ⨅ j, V j))
    (fun _ : Fin n => SheafOfModules.unit (structureSheafOfRings X)) _ _
    (fun j => overUnitHom (homOfLE (hle j)) (a j)) fun j => ?_⟩
  rw [SheafOfModules.overUnitHom_comp p (homOfLE (hle j)) (homOfLE (hVW j)) (a j) _ (ha j),
    ← SheafOfModules.overRestrict_eq_overUnitHom, Subsingleton.elim
      (homOfLE (hle j) ≫ homOfLE (hVW j)) (homOfLE (inf_le_left : _ ≤ W)),
    SheafOfModules.overRestrict_comp, SheafOfModules.overRestrict_map]

/-- **Stacks 08C6 over an open subset.** Let `p : 𝒢 ⟶ ℱ` be an epimorphism of `𝒪_X`-modules,
let `ℰ` be a direct summand of a finite free `𝒪_X`-module, and let `γ : ℰ|_W ⟶ ℱ|_W` be a map
defined over an open subset `W` of `X`. Then every point of `W` has a smaller open
neighbourhood over which `γ` factors through `p`.

Writing `ℰ` as a retract `(i, r)` of `𝒪_X^{⊕ n}`, it is enough to lift `r|_W ≫ γ` and compose
the lift with `i`, since `i ≫ r = 𝟙`. -/
public theorem exists_local_lift_over_of_isDirectSummandOfFiniteFree
    {E F G : StrictlyPerfect.OXMod.{u, u} X} (p : G ⟶ F) [Epi p]
    (hE : StrictlyPerfect.IsDirectSummandOfFiniteFree E) (W : Opens X.carrier)
    (γ : E.over W ⟶ F.over W) {x : X.carrier} (hx : x ∈ W) :
    ∃ W' : Opens X.carrier, ∃ hW' : W' ≤ W, x ∈ W' ∧
      ∃ l : E.over W' ⟶ G.over W', l ≫ (overFunctor (structureSheafOfRings X) W').map p =
        overRestrict (homOfLE hW') γ := by
  obtain ⟨n, ⟨ρ⟩⟩ := (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract E).mp hE
  -- `StrictlyPerfect.finiteFree X n` is by definition the biproduct of `n` copies of the
  -- structure sheaf as a module over itself; name the retract data at that description of it.
  obtain ⟨i, r, hir⟩ :
      ∃ (i : E ⟶ ⨁ fun _ : Fin n => SheafOfModules.unit (structureSheafOfRings X))
        (r : (⨁ fun _ : Fin n => SheafOfModules.unit (structureSheafOfRings X)) ⟶ E),
        i ≫ r = 𝟙 E :=
    ⟨ρ.i, ρ.r, ρ.retract⟩
  obtain ⟨W', hW'W, hxW', l, hl⟩ := exists_local_lift_over_biproduct_unit p W
    ((overFunctor (structureSheafOfRings X) W).map r ≫ γ) hx
  refine ⟨W', hW'W, hxW', (overFunctor (structureSheafOfRings X) W').map i ≫ l, ?_⟩
  rw [Category.assoc, hl, SheafOfModules.overRestrict_comp, SheafOfModules.overRestrict_map,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, hir,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- One of the degreewise lifting problems of the source proof of Stacks 08C7, solved over a
smaller open subset. Let `ℱ` be a complex of `𝒪_X`-modules with vanishing `i`-th cohomology
sheaf, let `𝒜` be a direct summand of a finite free `𝒪_X`-module and let `γ : 𝒜|_W ⟶ ℱ^i|_W` be
killed by the differential of `ℱ`. Then every point of `W` has a smaller open neighbourhood
over which `γ` factors through `ℱ^{i-1} ⟶ ℱ^i`.

Restriction preserves finite limits, so it carries the kernel fork exhibiting the cycles
`Z^i(ℱ)` to a kernel fork; hence `γ` factors through `Z^i(ℱ)|_W` because it is killed by the
differential. The map `ℱ^{i-1} ⟶ Z^i(ℱ)` is a global epimorphism by the vanishing of the
cohomology sheaf, so Stacks 08C6 over an open subset applies. -/
@[sga "6 I 1.3" "special case"]
public theorem exists_local_factorization_over
    {F : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ}
    {A : StrictlyPerfect.OXMod.{u, u} X}
    (hA : StrictlyPerfect.IsDirectSummandOfFiniteFree A) {i : ℤ}
    (hF : IsZero (F.homology i)) (W : Opens X.carrier) (γ : A.over W ⟶ (F.X i).over W)
    (hγ : γ ≫ (overFunctor (structureSheafOfRings X) W).map (F.d i (i + 1)) = 0)
    {x : X.carrier} (hx : x ∈ W) :
    ∃ W' : Opens X.carrier, ∃ hW' : W' ≤ W, x ∈ W' ∧ ∀ j : ℤ, j + 1 = i →
      ∃ l : A.over W' ⟶ (F.X j).over W',
        l ≫ (overFunctor (structureSheafOfRings X) W').map (F.d j i) =
          overRestrict (homOfLE hW') γ := by
  have hker : IsLimit ((KernelFork.ofι (F.iCycles i) (F.iCycles_d i (i + 1))).map
      (overFunctor (structureSheafOfRings X) W)) :=
    KernelFork.mapIsLimit _ (F.cyclesIsKernel i (i + 1) (by simp)) _
  obtain ⟨k, hk⟩ := KernelFork.IsLimit.lift' hker γ hγ
  simp only [KernelFork.map_ι, Fork.ι_ofι] at hk
  have hepi : Epi (F.toCycles (i - 1) i) :=
    epi_toCycles_of_isZero_homology (by omega) hF
  obtain ⟨W', hW'W, hxW', l, hl⟩ := exists_local_lift_over_of_isDirectSummandOfFiniteFree
    (F.toCycles (i - 1) i) hA W k hx
  refine ⟨W', hW'W, hxW', fun j hj => ?_⟩
  obtain rfl : j = i - 1 := by omega
  refine ⟨l, ?_⟩
  rw [← F.toCycles_i (i - 1) i, CategoryTheory.Functor.map_comp, ← Category.assoc, hl,
    ← SheafOfModules.overRestrict_map (homOfLE hW'W) (F.iCycles i),
    ← SheafOfModules.overRestrict_comp]
  exact congrArg (overRestrict (homOfLE hW'W)) hk

/-- The homotopy identity, in a single degree, is preserved by restriction to a smaller open
subset: restriction of morphisms between restrictions is additive, compatible with composition,
and takes the restriction of a global morphism to its restriction. -/
public theorem isNullHomotopyAt_overRestrict
    {E F : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ} (α : E ⟶ F)
    {W' W : Opens X.carrier} (f : W' ⟶ W)
    (h : ∀ p q : ℤ, q + 1 = p →
      ((overFunctor (structureSheafOfRings X) W).obj (E.X p) ⟶
        (overFunctor (structureSheafOfRings X) W).obj (F.X q)))
    {p : ℤ} (hp : CochainComplex.IsNullHomotopyAt ((restrictComplexOver X W).map α) h p) :
    CochainComplex.IsNullHomotopyAt ((restrictComplexOver X W').map α)
      (fun p q hq => overRestrict f (h p q hq)) p := by
  intro q r hq hr
  have h₀ := hp q r hq hr
  simp only [CategoryTheory.Functor.mapHomologicalComplex_map_f,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d] at h₀ ⊢
  rw [← SheafOfModules.overRestrict_map f (α.f p), h₀, SheafOfModules.overRestrict_add,
    SheafOfModules.overRestrict_comp, SheafOfModules.overRestrict_comp,
    SheafOfModules.overRestrict_map, SheafOfModules.overRestrict_map]

/-- The inductive step of Stacks 08C7, run `n` times: a point of `X` has an open neighbourhood
`W` carrying a family of maps between the restrictions to `W` of the terms of `ℰ` and `ℱ` which
satisfies the homotopy identity between `α` and the zero map in every degree above `b - n`.

The induction runs *downwards* from `b`. Having such a family over `W` in the degrees above `p`,
the map that remains to be factored in degree `p` is
`γ = α^p|_W - d_ℰ^p|_W ≫ h^{p+1}`, and `γ ≫ d_ℱ^p|_W = 0` follows from the homotopy identity
one degree up together with `d ≫ d = 0`. So `γ` is a lifting problem of the kind
`AlgebraicGeometry.RingedSpace.exists_local_factorization_over` solves, over a smaller open
neighbourhood `W'` of the point; its solution is the next value of the family, and the values
already built are carried from `W` to `W'` by `SheafOfModules.overRestrict`. -/
public theorem exists_local_isNullHomotopyAt
    {E F : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ} (α : E ⟶ F) (a b : ℤ)
    (hEa : ∀ p : ℤ, p < a → IsZero (E.X p)) (hEb : ∀ p : ℤ, b < p → IsZero (E.X p))
    (hEsummand : ∀ p : ℤ, StrictlyPerfect.IsDirectSummandOfFiniteFree (E.X p))
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) (x : X.carrier) (n : ℕ) :
    ∃ W : Opens X.carrier, x ∈ W ∧
      ∃ h : ∀ p q : ℤ, q + 1 = p →
          ((overFunctor (structureSheafOfRings X) W).obj (E.X p) ⟶
            (overFunctor (structureSheafOfRings X) W).obj (F.X q)),
        ∀ p : ℤ, b - n < p →
          CochainComplex.IsNullHomotopyAt ((restrictComplexOver X W).map α) h p := by
  classical
  induction n with
  | zero =>
    exact ⟨⊤, trivial, fun _ _ _ => 0, fun p hp => CochainComplex.isNullHomotopyAt_of_isZero _ _
      (CategoryTheory.Functor.map_isZero (overFunctor (structureSheafOfRings X) ⊤)
        (hEb p (by push_cast at hp; omega)))⟩
  | succ n ih =>
    obtain ⟨W, hxW, h, hh⟩ := ih
    by_cases hp₀ : a ≤ b - (n : ℤ)
    · -- The map that remains to be factored in degree `b - n` is killed by the differential of
      -- `ℱ`, because the homotopy identity holds one degree up and `d ≫ d = 0`.
      have hstep : h (b - n + 1) (b - n) rfl ≫
            (overFunctor (structureSheafOfRings X) W).map (F.d (b - n) (b - n + 1)) =
          (overFunctor (structureSheafOfRings X) W).map (α.f (b - n + 1)) -
            (overFunctor (structureSheafOfRings X) W).map (E.d (b - n + 1) (b - n + 2)) ≫
              h (b - n + 2) (b - n + 1) (by omega) :=
        eq_sub_of_add_eq
          (hh (b - n + 1) (by omega) (b - n) (b - n + 2) rfl (by omega)).symm
      have hγ : ((overFunctor (structureSheafOfRings X) W).map (α.f (b - n)) -
            (overFunctor (structureSheafOfRings X) W).map (E.d (b - n) (b - n + 1)) ≫
              h (b - n + 1) (b - n) rfl) ≫
          (overFunctor (structureSheafOfRings X) W).map (F.d (b - n) (b - n + 1)) = 0 := by
        rw [sub_comp, Category.assoc, hstep, ← CategoryTheory.Functor.map_comp, α.comm,
          CategoryTheory.Functor.map_comp, comp_sub, sub_sub_cancel, ← Category.assoc,
          ← CategoryTheory.Functor.map_comp, E.d_comp_d, CategoryTheory.Functor.map_zero,
          Limits.zero_comp]
      obtain ⟨W', hW'W, hxW', hlift⟩ := exists_local_factorization_over (hEsummand (b - n))
        (hF (b - n) hp₀) W _ hγ hxW
      refine ⟨W', hxW', Function.update (fun p q hq => overRestrict (homOfLE hW'W) (h p q hq))
        (b - n) (fun q hq => (hlift q hq).choose), fun p hp q r hq hr => ?_⟩
      rcases eq_or_lt_of_le (show b - (n : ℤ) ≤ p by push_cast at hp; omega) with rfl | hlt
      · obtain rfl : r = b - (n : ℤ) + 1 := by omega
        rw [Function.update_self, Function.update_of_ne (by omega)]
        simp only [CategoryTheory.Functor.mapHomologicalComplex_map_f,
          CategoryTheory.Functor.mapHomologicalComplex_obj_d]
        rw [(hlift q hq).choose_spec, SheafOfModules.overRestrict_sub,
          SheafOfModules.overRestrict_comp, SheafOfModules.overRestrict_map,
          SheafOfModules.overRestrict_map, sub_add_cancel]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact isNullHomotopyAt_overRestrict α (homOfLE hW'W) h
          (hh p (by push_cast at hp ⊢; omega)) q r hq hr
    · -- Below `a` the terms of `ℰ` vanish, so nothing has to be extended.
      refine ⟨W, hxW, h, fun p hp => ?_⟩
      rcases eq_or_lt_of_le (show b - (n : ℤ) ≤ p by push_cast at hp; omega) with rfl | hlt
      · exact CochainComplex.isNullHomotopyAt_of_isZero _ _
          (CategoryTheory.Functor.map_isZero (overFunctor (structureSheafOfRings X) W)
            (hEa _ (by omega)))
      · exact hh p (by push_cast at hp ⊢; omega)

end AlgebraicGeometry.RingedSpace

end
