module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas

/-!
# Local lifting of maps out of a direct summand of a finite free module

Let `X` be a ringed space and let `p : 𝒢 ⟶ ℱ` be a surjective map of `𝒪_X`-modules. A map
`f : ℰ ⟶ ℱ` out of a direct summand of a finite free `𝒪_X`-module lifts through `p` after
restricting to a small enough open neighbourhood of any point of `X` (Stacks 08C6).

## Main results

* `CategoryTheory.Functor.retractMapBiproduct_i_desc`: for an additive functor `F`, a map
  `F(⨁ c) ⟶ F Z` assembled from the images of the components of `q : ⨁ c ⟶ Z` through
  `CategoryTheory.Functor.retractMapBiproduct` is `F q`, and
  `CategoryTheory.Functor.retractMapBiproduct_i_desc_comp` is its form for lifting `F q`
  through a map `F p` componentwise.
* `AlgebraicGeometry.RingedSpace.exists_local_section_of_epi`: an epimorphism of
  `𝒪_X`-modules is surjective on sections after shrinking the open set around a point.
* `AlgebraicGeometry.RingedSpace.exists_local_lift_biproduct_structureModule`: the case
  `ℰ = 𝒪_X^{⊕ n}` of Stacks 08C6, where the data of the map is `n` global sections.
* `AlgebraicGeometry.RingedSpace.exists_local_lift_of_isDirectSummandOfFiniteFree` is
  Stacks 08C6.

## Implementation notes

Restriction to an open subspace is `AlgebraicGeometry.RingedSpace.restrictModules`, the
formulation of `StacksFrontier/AlgebraicGeometry/PseudoCoherent/SheafLevel.lean`, rather than
`SheafOfModules.overFunctor`; the two are equivalent, but the former is the one the rest of
the pseudo-coherence development is phrased in.

Surjectivity of `p` is expressed categorically as `Epi p`, and
`SheafOfModules.isLocallySurjective_toSheaf_of_epi` turns that into local surjectivity on
sections, which is the form the source proof uses (Stacks 007S).

The source reduces to `ℰ = 𝒪_X^{⊕ n}`, where a map to `ℱ` is `n` global sections of `ℱ` and
lifting it is lifting those sections. Formally the reduction runs the other way round, which
avoids producing an isomorphism: a retract `ρ : Retract ℰ 𝒪_X^{⊕ n}` lets one lift `ρ.r ≫ f`
instead of `f` and compose the resulting lift with `ρ.i`, since `ρ.i ≫ ρ.r = 𝟙`.

A map *out of* the restriction of `𝒪_X^{⊕ n}` is assembled from the restrictions of the
lifted components through `CategoryTheory.Functor.retractMapBiproduct`: restriction need not
*preserve* the biproduct, it is enough that the restriction of `𝒪_X^{⊕ n}` is a retract of
`𝒪_U^{⊕ n}`, because the comparison morphism of that retract points in the direction a map
out of the restricted biproduct needs. This avoids the preservation-of-limits route, which
for `SheafOfModules.pushforward` goes through
`SheafOfModules.pullbackPushforwardAdjunction` and is expensive to elaborate.

## References

* [The Stacks Project, Lemma 20.46.4 (08C6)](https://stacks.math.columbia.edu/tag/08C6)
* [The Stacks Project, Section 6.16 (007S)](https://stacks.math.columbia.edu/tag/007S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Let `F` be an additive functor and `q : ⨁ c ⟶ Z` a map out of a finite biproduct. The
map `F (⨁ c) ⟶ F Z` obtained by exhibiting `F (⨁ c)` as a retract of `⨁ F c`
(`CategoryTheory.Functor.retractMapBiproduct`) and then using the images `F (ι j ≫ q)` of
the components of `q` on the summands is again `F q`.

Indeed the composite is `∑ j, F (π j) ≫ F (ι j ≫ q) = F ((∑ j, π j ≫ ι j) ≫ q)`, and
`∑ j, π j ≫ ι j` is the identity. This is how a map out of `F (⨁ c)` is built when `F` does
not preserve the biproduct. -/
theorem retractMapBiproduct_i_desc [Preadditive C] [Preadditive D] {J : Type} [Fintype J]
    (F : C ⥤ D) [F.Additive] (c : J → C) [HasBiproduct c] [HasBiproduct (F.obj ∘ c)] {Z : C}
    (q : (⨁ c) ⟶ Z) :
    (F.retractMapBiproduct c).i ≫ biproduct.desc (fun j => F.map (biproduct.ι c j ≫ q)) =
      F.map q := by
  change F.biproductComparison c ≫
    biproduct.desc (fun j => F.map (biproduct.ι c j ≫ q)) = F.map q
  rw [CategoryTheory.Functor.biproductComparison, biproduct.lift_desc,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
      (F.map_comp (biproduct.π c j) (biproduct.ι c j ≫ q)).symm,
    ← CategoryTheory.Functor.map_sum]
  congr 1
  simp only [← Category.assoc]
  rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp]

/-- The form in which `CategoryTheory.Functor.retractMapBiproduct_i_desc` is used: if each
component `F (ι j ≫ q)` of `F q` has been lifted through `F p` to a map `b j`, then the map
`F (⨁ c) ⟶ F W` assembled from the `b j` is a lift of `F q` through `F p`. -/
theorem retractMapBiproduct_i_desc_comp [Preadditive C] [Preadditive D] {J : Type} [Fintype J]
    (F : C ⥤ D) [F.Additive] (c : J → C) [HasBiproduct c] [HasBiproduct (F.obj ∘ c)]
    {W Z : C} (q : (⨁ c) ⟶ Z) (p : W ⟶ Z) (b : ∀ j, (F.obj ∘ c) j ⟶ F.obj W)
    (hb : ∀ j, b j ≫ F.map p = F.map (biproduct.ι c j ≫ q)) :
    ((F.retractMapBiproduct c).i ≫ biproduct.desc b) ≫ F.map p = F.map q :=
  calc ((F.retractMapBiproduct c).i ≫ biproduct.desc b) ≫ F.map p
      = (F.retractMapBiproduct c).i ≫ (biproduct.desc b ≫ F.map p) := Category.assoc _ _ _
    _ = (F.retractMapBiproduct c).i ≫ biproduct.desc fun j => F.map (biproduct.ι c j ≫ q) := by
        refine congrArg _ (biproduct.hom_ext' _ _ fun j => ?_)
        rw [← Category.assoc, biproduct.ι_desc, biproduct.ι_desc, hb j]
    _ = F.map q := F.retractMapBiproduct_i_desc c q

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}}

/-- An open subset of an open subspace `U` of `X`, viewed as an open subset of `X`, is
contained in `U`. -/
theorem isOpenEmbedding_functor_obj_le (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    U.isOpenEmbedding.functor.obj V ≤ U := by
  rintro y ⟨z, -, rfl⟩
  exact z.2

/-- A section of an `𝒪_X`-module over an open set `W` of `X` gives a global section of the
restriction of that module to any open subspace `U ≤ W`, namely the family of its
restrictions to the open subsets of `U`. -/
def sectionsRestrictModules {M : StrictlyPerfect.OXMod.{u, u, u} X} {U W : Opens X.carrier}
    (hUW : U ≤ W) (a : M.val.obj (op W)) : ((restrictModules X U).obj M).sections :=
  PresheafOfModules.sectionsMk
    (fun V : (Opens (X.restrict U.isOpenEmbedding).carrier)ᵒᵖ =>
      M.val.map (homOfLE ((isOpenEmbedding_functor_obj_le U V.unop).trans hUW)).op a)
    (fun V V' g => by
      change M.val.map (U.isOpenEmbedding.functor.map g.unop).op
          (M.val.map (homOfLE ((isOpenEmbedding_functor_obj_le U V.unop).trans hUW)).op a) =
        M.val.map (homOfLE ((isOpenEmbedding_functor_obj_le U V'.unop).trans hUW)).op a
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) a)

/-- An epimorphism `p : 𝒢 ⟶ ℱ` of `𝒪_X`-modules is locally surjective on sections: a global
section of `ℱ` is, on some open neighbourhood of any given point, the image of a section of
`𝒢`. This is the sheaf-theoretic surjectivity of Stacks 007S. -/
theorem exists_local_section_of_epi {F G : StrictlyPerfect.OXMod.{u, u, u} X} (p : G ⟶ F) [Epi p]
    (σ : F.sections) (x : X.carrier) :
    ∃ V : Opens X.carrier, x ∈ V ∧ ∃ a : G.val.obj (op V), p.val.app (op V) a = σ.val (op V) := by
  have hp : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (StrictlyPerfect.structureSheafOfRings X)).map p).hom :=
    SheafOfModules.isLocallySurjective_toSheaf_of_epi p
  obtain ⟨V, hVtop, ⟨a, ha⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp hp ⊤ (σ.val (op ⊤)) x (by simp)
  exact ⟨V, hxV, a, (ha : p.val.app (op V) a = F.val.map (homOfLE hVtop).op (σ.val (op ⊤))).trans
    (σ.property (homOfLE hVtop).op)⟩

/-- Let `p : 𝒢 ⟶ ℱ` be a map of `𝒪_X`-modules and let `g : 𝒪_X ⟶ ℱ` be classified by a
global section of `ℱ`. If a section `a` of `𝒢` over `W` is carried by `p` to that global
section, then over any open subspace `U ≤ W` the map classified by the restriction of `a` is
a lift of `g` through `p`. -/
theorem unitHomEquiv_symm_sectionsRestrictModules_comp
    {F G : StrictlyPerfect.OXMod.{u, u, u} X} (p : G ⟶ F) {U W : Opens X.carrier} (hUW : U ≤ W)
    {a : G.val.obj (op W)} (g : StrictlyPerfect.structureModule X ⟶ F)
    (hag : p.val.app (op W) a = (F.unitHomEquiv g).val (op W)) :
    ((restrictModules X U).obj G).unitHomEquiv.symm (sectionsRestrictModules hUW a) ≫
      (restrictModules X U).map p = (restrictModules X U).map g := by
  refine ((restrictModules X U).obj F).unitHomEquiv.injective ?_
  rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
  refine PresheafOfModules.sections_ext _ _ fun V => ?_
  have hle : U.isOpenEmbedding.functor.obj V.unop ≤ W :=
    (isOpenEmbedding_functor_obj_le U V.unop).trans hUW
  change p.val.app (op (U.isOpenEmbedding.functor.obj V.unop)) (G.val.map (homOfLE hle).op a) =
    g.val.app (op (U.isOpenEmbedding.functor.obj V.unop))
      (1 : (StrictlyPerfect.structureSheafOfRings X).obj.obj
        (op (U.isOpenEmbedding.functor.obj V.unop)))
  rw [PresheafOfModules.naturality_apply, hag]
  exact (F.unitHomEquiv g).property (homOfLE hle).op

/-- Stacks 08C6 for the finite free module `𝒪_X^{⊕ n} = ⨁ (fun _ : Fin n => 𝒪_X)`: a map
`q : 𝒪_X^{⊕ n} ⟶ ℱ` lifts through an epimorphism `p : 𝒢 ⟶ ℱ` on an open neighbourhood of any
point.

The map `q` is the same data as its `n` components `𝒪_X ⟶ ℱ`, that is, `n` global sections
of `ℱ`; each is the image of a section of `𝒢` on some neighbourhood of the given point, and
`U` is the intersection of those finitely many neighbourhoods. -/
theorem exists_local_lift_biproduct_structureModule {F G : StrictlyPerfect.OXMod.{u, u, u} X}
    {n : ℕ} (q : (⨁ fun _ : Fin n => StrictlyPerfect.structureModule X) ⟶ F) (p : G ⟶ F) [Epi p]
    (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ l : (restrictModules X U).obj (⨁ fun _ : Fin n => StrictlyPerfect.structureModule X) ⟶
        (restrictModules X U).obj G,
        l ≫ (restrictModules X U).map p = (restrictModules X U).map q := by
  classical
  choose V hxV a ha using fun j : Fin n => exists_local_section_of_epi p
    (F.unitHomEquiv (biproduct.ι (fun _ : Fin n => StrictlyPerfect.structureModule X) j ≫ q)) x
  have hxU : x ∈ (⨅ j, V j : Opens X.carrier) := by
    change x ∈ (↑(⨅ j, V j) : Set X.carrier)
    rw [Opens.coe_iInf, Set.mem_iInter]
    exact hxV
  obtain ⟨b, hb⟩ : ∃ b : ∀ j : Fin n,
      ((restrictModules X (⨅ j, V j)).obj ∘
        fun _ : Fin n => StrictlyPerfect.structureModule X) j ⟶
          (restrictModules X (⨅ j, V j)).obj G,
      ∀ j, b j ≫ (restrictModules X (⨅ j, V j)).map p =
        (restrictModules X (⨅ j, V j)).map
          (biproduct.ι (fun _ : Fin n => StrictlyPerfect.structureModule X) j ≫ q) :=
    ⟨fun j => ((restrictModules X (⨅ j, V j)).obj G).unitHomEquiv.symm
        (sectionsRestrictModules (iInf_le V j) (a j)),
      fun j => unitHomEquiv_symm_sectionsRestrictModules_comp p _ _ (ha j)⟩
  exact ⟨⨅ j, V j, hxU, _, CategoryTheory.Functor.retractMapBiproduct_i_desc_comp
    (restrictModules X (⨅ j, V j)) _ q p b hb⟩

/-- **Stacks 08C6.** Let `X` be a ringed space, let `p : 𝒢 ⟶ ℱ` be an epimorphism of
`𝒪_X`-modules and let `f : ℰ ⟶ ℱ` be a map out of a direct summand of a finite free
`𝒪_X`-module. Then every point of `X` has an open neighbourhood over which `f` factors
through `p`.

Writing `ℰ` as a retract `(i, r)` of `𝒪_X^{⊕ n}`, it is enough to lift `r ≫ f` and compose
the lift with `i`, since `i ≫ r = 𝟙`. -/
@[stacks 08C6 "all three universes collapsed (space = ring = module), stated through \
`restrictModules`. The module-universe-free form is in \
`StacksFrontier/Algebra/Homology/StrictlyPerfectLiftModuleUniverse.lean`; neither subsumes \
the other."]
theorem exists_local_lift_of_isDirectSummandOfFiniteFree
    {E F G : StrictlyPerfect.OXMod.{u, u, u} X} (f : E ⟶ F) (p : G ⟶ F) [Epi p]
    (hE : StrictlyPerfect.IsDirectSummandOfFiniteFree E) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ l : (restrictModules X U).obj E ⟶ (restrictModules X U).obj G,
        l ≫ (restrictModules X U).map p = (restrictModules X U).map f := by
  intro x
  obtain ⟨n, ⟨ρ⟩⟩ := (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract E).mp hE
  -- `StrictlyPerfect.finiteFree X n` is by definition `⨁ (fun _ : Fin n => 𝒪_X)`; name the
  -- retract data at that description of it.
  obtain ⟨i, r, hir⟩ :
      ∃ (i : E ⟶ ⨁ fun _ : Fin n => StrictlyPerfect.structureModule X)
        (r : (⨁ fun _ : Fin n => StrictlyPerfect.structureModule X) ⟶ E), i ≫ r = 𝟙 E :=
    ⟨ρ.i, ρ.r, ρ.retract⟩
  obtain ⟨U, hxU, l, hl⟩ := exists_local_lift_biproduct_structureModule (r ≫ f) p x
  refine ⟨U, hxU, (restrictModules X U).map i ≫ l, ?_⟩
  rw [Category.assoc, hl, ← (restrictModules X U).map_comp, ← Category.assoc, hir,
    Category.id_comp]

end AlgebraicGeometry.RingedSpace

end
