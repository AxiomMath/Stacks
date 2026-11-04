module

public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedAugmentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekReduction
import StacksCore.Tactic.StacksAttribute

/-!
# The lower shrieks of the simplicial semi-representable ringed sites

Let `(C, O_C)` be a ringed site and let `K` be a simplicial semi-representable object of `C`.
Stacks 0D9W records, besides the total ringed site and its augmentations, three left adjoints of
inverse images of sheaves of modules: the functor `a_! : Mod(O) ⥤ Mod(O_C)` left adjoint to `a^*`
of its item (4), the degreewise `a_{n!} : Mod(O_n) ⥤ Mod(O_C)` left adjoint to `a_n^*`, and the
`f_{φ!} : Mod(O_n) ⥤ Mod(O_m)` left adjoint to `f_φ^*` attached to a simplex map `φ : [m] ⟶ [n]`.
It also records the morphism of ringed topoi `g_n : (Sh(C/K_n), O_n) ⟶ (Sh((C/K)_total), O)`,
its flatness, and the left adjoint `g_{n!}` of `g_n^*`.

This file supplies those, each adjoint with its adjunction.

## Main definitions

* `CategoryTheory.SemiRepresentable.Simplicial.totalLowerShriek` and
  `.totalInverseImageModules`: `a_!` and `a^*` for the total ringed site.
* `CategoryTheory.SemiRepresentable.Simplicial.totalLowerShriekAdjunction`: `a_! ⊣ a^*`.
* `CategoryTheory.SemiRepresentable.Simplicial.degreewiseLowerShriek`,
  `.degreewiseInverseImageModules` and `.degreewiseLowerShriekAdjunction`: `a_{n!} ⊣ a_n^*`.
* `CategoryTheory.SemiRepresentable.Simplicial.transitionLowerShriek`,
  `.transitionInverseImageModules` and `.transitionLowerShriekAdjunction`: `f_{φ!} ⊣ f_φ^*`.
* `CategoryTheory.SemiRepresentable.Simplicial.fibreFactor`, `.fibreArrow`: the two halves of
  the factorisation of an arrow of the total site into an object of simplicial degree `n`.
* `CategoryTheory.SemiRepresentable.Simplicial.componentRingedTopos`: the degree-`n` component
  of the total ringed site, with the structure sheaf `g_n⁻¹O`.
* `CategoryTheory.SemiRepresentable.Simplicial.componentMorphismOfTopoi`,
  `.componentInverseImageCommRingIso`, `.componentCommRingFsharpAdjoint` and
  `.componentRingedMorphism`: the morphism of ringed topoi `g_n`.
* `CategoryTheory.SemiRepresentable.Simplicial.componentLowerShriek`,
  `.componentInverseImageModules` and `.componentLowerShriekAdjunction`: `g_{n!} ⊣ g_n^*`.
* `CategoryTheory.SemiRepresentable.Simplicial.localizationReduction`,
  `.relocalizationReduction` and `.componentInclusionReduction`: the reduction data of
  `Stacks.Sites.ReducedLowerShriek.Reduction` for the three functors of sites, which is what
  makes the three lower shrieks exact.
* `CategoryTheory.SemiRepresentable.Simplicial.componentFibre` and `.relocalizationFibre`: the
  index sets of the connected components of the structured-arrow categories of the component
  inclusion and of the relocalization functor.

## Main results

* `CategoryTheory.SemiRepresentable.Simplicial.localizationFunctor_isContinuous'`,
  `.localizationFunctor_isCocontinuous'`, `.relocalizationFunctor_isContinuous'` and
  `.relocalizationFunctor_isCocontinuous'`: the Stacks 0D85 continuity and cocontinuity of the
  localization and relocalization functors, with their topologies spelled as
  `componentwiseTopology` rather than through the `LocalizationSites` projections.
* `CategoryTheory.SemiRepresentable.Simplicial.relocalizationFunctor_comp_localizationFunctor`:
  the relocalization functor followed by the localization functor of its target is the
  localization functor of its source.
* `CategoryTheory.SemiRepresentable.Simplicial.componentInclusion_isCocontinuous` and
  `.componentInclusion_isContinuous`: the inclusion of the degree-`n` componentwise localization
  into the total localization site is cocontinuous and continuous.
* `CategoryTheory.SemiRepresentable.Simplicial.fibreFactor_comp`: every arrow of the total site
  into an object of simplicial degree `n` factors through the image of an arrow of the degree-`n`
  componentwise localization.
* `CategoryTheory.SemiRepresentable.Simplicial.componentRingedMorphism_isFlat`: `g_n` is flat.
* `CategoryTheory.SemiRepresentable.Simplicial.componentInclusion_comp_totalLocalizationFunctor_eq`
  states that the component inclusion followed by `j_total` is the localization functor of `K_n`,
  which is why the structure sheaf `g_n⁻¹O` of `componentRingedTopos` is the `O_n` of Stacks 0D9U.
* `CategoryTheory.SemiRepresentable.Simplicial.exactFunctor_degreewiseLowerShriek`,
  `.exactFunctor_transitionLowerShriek` and `.exactFunctor_componentLowerShriek`: the three
  exactness assertions of Stacks 0D9W, `a_{n!}`, `f_{φ!}` and `g_{n!}` are exact.

## Implementation notes

All three adjunctions are the same statement — Stacks 0797, `Stacks.SheafOfModules.lowerShriek`
and `.lowerShriekAdjunction` — at three continuous and cocontinuous functors of sites: the total
localization functor `j_total`, the semi-representable localization functor `j_n : C/K_n ⥤ C`,
and the componentwise relocalization functor `C/K_n ⥤ C/K_m` of `K(φ)`. That is exactly the
source's own justification: `a_!` exists "because `a^{-1}O_C = O` and we can replace the use of
Modules on Sites, Lemma 18.16.2 in the proof of Lemma 85.16.2 by Modules on Sites, Lemma 18.41.1",
and Lemma 18.41.1 is Tag 0797. Cocontinuity of the site functor is what makes restriction along it
the inverse image `a^{-1}`, which by `O = a^{-1}O_C` is `a^*`; this is the reading recorded in the
module documentation of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LowerShriek.lean`.

For the total and the degreewise shriek the sheaf of rings on the source that Tag 0797 produces,
`Stacks.SheafOfModules.inverseImageRing`, is on the nose the library's structure sheaf — the
pulled-back ring sheaf of the total ringed site, respectively the ring sheaf of the degree-`n`
localization ringed topos — so the types above are ascribed with the library's names. For the
transition it is `f_φ⁻¹O_m`, which is `O_n` but not by `rfl`: the two restrictions are taken along
`relocalizationFunctor ⋙ j_m` and along `j_n`, which are equal functors by
`relocalizationFunctor_comp_localizationFunctor` and not definitionally equal, `Sigma.desc` of a
composite being a different term from the composite of the `Sigma.desc`s. The identification of
`f_φ⁻¹O_m` with `O_n` is the structure map of Stacks 0D9U's `familyMorphism`, which that tag
records as an isomorphism.

The continuity and cocontinuity helpers take the site and its topology directly rather than a
ringed site. With a ringed site `X : RingedSite.{u, v, max x u v w}` as the argument, instance
search has to solve `max x u v ?w =?= max x u v w` to use them, which Lean's universe unifier
does not do, and every use site fails with a stuck universe constraint.

## Exactness

The source asserts more than the three adjunctions: `a_{n!}`, `f_{φ!}` and `g_{n!}` are *exact*.
All three are proved, as `exactFunctor_degreewiseLowerShriek`,
`exactFunctor_transitionLowerShriek` and `exactFunctor_componentLowerShriek`, and all three are
one general theorem instantiated three times:
`Stacks.Sites.ReducedLowerShriek.lowerShriek_exact`, which makes lower shriek exact as soon as
every connected component of the category of `u`-structured arrows out of an object has a
terminal object along which the sheaf of rings is invertible. That is the direct-sum formula for
lower shriek of presheaves of modules: the sections over `V` are the sum, over the components,
of the sections at the terminal objects, and a direct sum of injective maps of modules is
injective.

The reduction data is supplied here, once per functor of sites:

* `localizationReduction` for `j_n : C/K_n ⥤ C`, where the component of `(c, V ⟶ c.left)` is the
  pair `(i, V ⟶ c.left ⟶ K_{n,i})` and its terminal object is `(V ⟶ K_{n,i}, 𝟙 V)` — every arrow
  of the ambient site into the underlying object of `c` *is* an object of the slice site.
* `relocalizationReduction` for `C/K_n ⥤ C/K_m`, the same with the arrows taken under `K(φ)`.
* `componentInclusionReduction` for `C/K_n ⥤ (C/K)_total`, where the component of
  `(c, Z ⟶ g_n(c))` is the triple `componentFibre` of a component of `K_n`, the simplex map
  `Z.right ⟶ [n]` carried by the structure arrow, and the composite underlying arrow of the
  ambient site; its terminal object is `fibreFactor`, and the arrow to the original structured
  arrow is `fibreArrow`.

For `g_{n!}` this is Stacks 0D74 in the `Comma`-category model of the total site, and the
simplex maps indexing the components of `componentFibre` are the `φ : [n] ⟶ [m]` of the
direct-sum formula of Tag 0D72. The flatness hypothesis the source's proof of 0D74 uses is not
needed in this model: the structure sheaf of the total site is pulled back from the ambient site,
so it does not see the arrow along which a summand is taken, which is what
`isIso_pulledBackRingSheaf_map_of_left_id` records.

The decomposition argument of Stacks 0D9U — presenting `Mod(O_{K_n})` as `∏_i Mod(O_{U_i})` and
the shriek as `(F_i) ↦ ⊕_i j_{i!}F_i` — is not the route taken. The direct-sum formula of the
general theorem is that decomposition and the single-slice extension by zero at once, so running
it once covers all three functors of sites, including the component inclusion, which is not a
disjoint union of slice localizations of the total site and so is out of reach of the
decomposition.

## References

* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 0D74](https://stacks.math.columbia.edu/tag/0D74)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SemiRepresentable

universe x u v w r

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  componentwiseTopology_hasSheafCompose_forget₂

namespace CategoryTheory.SemiRepresentable.Simplicial

/-- The localization functor of a semi-representable object is continuous, with the source
topology written as a `componentwiseTopology`. -/
theorem localizationFunctor_isContinuous' {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (L : FormalCoproduct.{x} C) :
    (⟨L, L, 𝟙 L⟩ : LocalizationSites.{x} C J).localizationFunctor.IsContinuous
      (componentwiseTopology J L) J := by
  simpa [LocalizationSites.sourceTopology] using
    LocalizationSites.localizationFunctor_isContinuous
      (⟨L, L, 𝟙 L⟩ : LocalizationSites.{x} C J)

/-- The localization functor of a semi-representable object is cocontinuous, with the source
topology written as a `componentwiseTopology`. -/
theorem localizationFunctor_isCocontinuous' {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (L : FormalCoproduct.{x} C) :
    (⟨L, L, 𝟙 L⟩ : LocalizationSites.{x} C J).localizationFunctor.IsCocontinuous
      (componentwiseTopology J L) J := by
  simpa [LocalizationSites.sourceTopology] using
    LocalizationSites.localizationFunctor_isCocontinuous
      (⟨L, L, 𝟙 L⟩ : LocalizationSites.{x} C J)

/-- The relocalization functor of a morphism of semi-representable objects is continuous, with
both topologies written as `componentwiseTopology`. -/
theorem relocalizationFunctor_isContinuous' {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {L M : FormalCoproduct.{x} C} (f : L ⟶ M) :
    (⟨L, M, f⟩ : LocalizationSites.{x} C J).relocalizationFunctor.IsContinuous
      (componentwiseTopology J L) (componentwiseTopology J M) := by
  simpa [LocalizationSites.sourceTopology, LocalizationSites.targetTopology] using
    LocalizationSites.relocalizationFunctor_isContinuous
      (⟨L, M, f⟩ : LocalizationSites.{x} C J)

/-- The relocalization functor of a morphism of semi-representable objects is cocontinuous, with
both topologies written as `componentwiseTopology`. -/
theorem relocalizationFunctor_isCocontinuous' {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {L M : FormalCoproduct.{x} C} (f : L ⟶ M) :
    (⟨L, M, f⟩ : LocalizationSites.{x} C J).relocalizationFunctor.IsCocontinuous
      (componentwiseTopology J L) (componentwiseTopology J M) := by
  simpa [LocalizationSites.sourceTopology, LocalizationSites.targetTopology] using
    LocalizationSites.relocalizationFunctor_isCocontinuous
      (⟨L, M, f⟩ : LocalizationSites.{x} C J)

attribute [local instance] localizationFunctor_isContinuous'
  localizationFunctor_isCocontinuous' relocalizationFunctor_isContinuous'
  relocalizationFunctor_isCocontinuous'

variable (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
  (K : SimplicialObject (FormalCoproduct.{x} X.C))

/-- The lower shriek `a_! : Mod(O) ⥤ Mod(O_C)` of the total ringed site: a sheaf of `O`-modules
on the total localization site is pushed forward as a presheaf of modules along `j_total` and the
result is sheafified. -/
def totalLowerShriek :
    SheafOfModules.{max x u v w} (pulledBackRingSheaf X K) ⥤
      SheafOfModules.{max x u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Stacks.SheafOfModules.lowerShriek.{max x u v w, max x u v w, v, max x u v, v, u}
    (totalLocalizationTopology K X.J) X.J (totalLocalizationFunctor K)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- The inverse image `a^* = a^{-1} : Mod(O_C) ⥤ Mod(O)` of the total augmentation: a sheaf of
`O_C`-modules is restricted along `j_total` and read as a sheaf of modules over
`O = a^{-1}O_C`. -/
def totalInverseImageModules :
    SheafOfModules.{max x u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{max x u v w} (pulledBackRingSheaf X K) :=
  Stacks.SheafOfModules.inverseImage.{max x u v w, max x u v w, v, max x u v, v, u}
    (totalLocalizationTopology K X.J) X.J (totalLocalizationFunctor K)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- **Stacks 0D9W, item (4).** For a simplicial semi-representable object `K` of the underlying
site of a ringed site `X`, the inverse image `a^*` of sheaves of modules along the augmentation of
the total ringed site has a left adjoint `a_! : Mod(O) ⥤ Mod(O_C)`. -/
@[stacks 0D9W "lower_shriek"]
def totalLowerShriekAdjunction :
    totalLowerShriek.{x, u, v, w} X K ⊣ totalInverseImageModules.{x, u, v, w} X K :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{max x u v w, max x u v w, v, max x u v, v, u}
    (totalLocalizationTopology K X.J) X.J (totalLocalizationFunctor K)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

variable (n : SimplexCategory)

/-- The degreewise lower shriek `a_{n!} : Mod(O_n) ⥤ Mod(O_C)`: a sheaf of `O_n`-modules on the
degree-`n` localization is pushed forward as a presheaf of modules along `j_n` and sheafified. -/
def degreewiseLowerShriek :
    SheafOfModules.{max x u v w} (Stacks.SheafOfModules.Tensor.ringSheaf
        (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op n))).O) ⥤
      SheafOfModules.{max x u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Stacks.SheafOfModules.lowerShriek.{max x u v w, max x u v w, max x u v, max x u v, v, u}
    (componentwiseTopology X.J (K.obj (op n))) X.J
    (⟨K.obj (op n), K.obj (op n), 𝟙 _⟩ :
      LocalizationSites.{x} X.C X.J).localizationFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- The inverse image `a_n^* = a_n^{-1} : Mod(O_C) ⥤ Mod(O_n)` of the degreewise augmentation. -/
def degreewiseInverseImageModules :
    SheafOfModules.{max x u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{max x u v w} (Stacks.SheafOfModules.Tensor.ringSheaf
        (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op n))).O) :=
  Stacks.SheafOfModules.inverseImage.{max x u v w, max x u v w, max x u v, max x u v, v, u}
    (componentwiseTopology X.J (K.obj (op n))) X.J
    (⟨K.obj (op n), K.obj (op n), 𝟙 _⟩ :
      LocalizationSites.{x} X.C X.J).localizationFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- **Stacks 0D9W, the degreewise lower shriek.** The inverse image `a_n^*` of sheaves of modules
along the degreewise augmentation `a_n : (Sh(C/K_n), O_n) ⟶ (Sh(C), O_C)` has a left adjoint
`a_{n!} : Mod(O_n) ⥤ Mod(O_C)`.

Exactness of `a_{n!}`, which the source asserts as well, is
`CategoryTheory.SemiRepresentable.Simplicial.exactFunctor_degreewiseLowerShriek`. -/
@[stacks 0D9W "degreewise_lower_shriek_adjunction"]
def degreewiseLowerShriekAdjunction :
    degreewiseLowerShriek.{x, u, v, w} X K n ⊣
      degreewiseInverseImageModules.{x, u, v, w} X K n :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{max x u v w, max x u v w, max x u v,
      max x u v, v, u}
    (componentwiseTopology X.J (K.obj (op n))) X.J
    (⟨K.obj (op n), K.obj (op n), 𝟙 _⟩ :
      LocalizationSites.{x} X.C X.J).localizationFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- **The reduction data of the localization functor of a semi-representable object.** A
structured arrow `(c, V ⟶ j(c))` out of `V` lies in the connected component indexed by the
composite `V ⟶ c.left ⟶ L_i` of its structure arrow with the structure arrow of `c`, and the
terminal object of that component is the arrow `(V ⟶ L_i, 𝟙 V)`: every arrow of the ambient site
into the underlying object of `c` *is* an object of the slice over `L_i`. -/
noncomputable def localizationReduction {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (L : FormalCoproduct.{x} C) (O : Cᵒᵖ ⥤ RingCat.{w}) :
    Stacks.Sites.ReducedLowerShriek.Reduction.{max x v}
      (⟨L, L, 𝟙 L⟩ : LocalizationSites.{x} C J).localizationFunctor O where
  idx V := Σ i : L.I, (V ⟶ L.obj i)
  pt {V} t := StructuredArrow.mk (Y := (⟨t.1, Over.mk t.2⟩ : ComponentOver L)) (𝟙 V)
  red {V} s := ⟨s.right.1, s.hom ≫ s.right.2.hom⟩
  lift {V} s := StructuredArrow.homMk
    (CategoryTheory.Sigma.SigmaHom.mk
      (Over.homMk s.hom : Over.mk (s.hom ≫ s.right.2.hom) ⟶ s.right.2))
    (Category.id_comp _)
  red_eq := by
    rintro V ⟨i, h⟩ ⟨sl, ⟨j, Y⟩, sh⟩ ⟨gl, ⟨a⟩, gw⟩
    have hsh : sh = a.left := by
      have hw : 𝟙 V ≫ sh = 𝟙 V ≫ a.left := gw
      simpa using hw
    refine congrArg (fun k => (⟨i, k⟩ : Σ i : L.I, (V ⟶ L.obj i))) ?_
    rw [hsh]
    exact Over.w a
  hom_ext := by
    rintro V ⟨i, h⟩ ⟨sl, ⟨j, Y⟩, sh⟩ ⟨gl, ⟨a⟩, gw⟩ ⟨gl', ⟨a'⟩, gw'⟩
    have h1 : sh = a.left := by
      have hw : 𝟙 V ≫ sh = 𝟙 V ≫ a.left := gw
      simpa using hw
    have h2 : sh = a'.left := by
      have hw : 𝟙 V ≫ sh = 𝟙 V ≫ a'.left := gw'
      simpa using hw
    rw [StructuredArrow.hom_eq_iff]
    exact congrArg CategoryTheory.Sigma.SigmaHom.mk
      (Over.OverMorphism.ext (h1.symm.trans h2))
  isIso_map {V} _ := by
    change IsIso (O.map (𝟙 (op V)))
    rw [O.map_id]
    infer_instance

/-- **Stacks 0D9W, exactness of the degreewise lower shriek.** The functor
`a_{n!} : Mod(O_n) ⥤ Mod(O_C)` left adjoint to the inverse image `a_n^*` of the degreewise
augmentation is exact.

Right exactness is formal, `a_{n!}` being a left adjoint. Left exactness is the direct-sum
formula: the sections of `a_{n!}G` over `V` are the sum, over the pairs `(i, V ⟶ K_{n,i})`, of
the sections of `G` at the corresponding object of the slice site, so `a_{n!}` is injective on
sections as soon as `G ⟶ G'` is. That is the content of
`Stacks.Sites.ReducedLowerShriek.lowerShriek_exact` at the reduction data
`CategoryTheory.SemiRepresentable.Simplicial.localizationReduction`. -/
@[stacks 0D9W "degreewise_lower_shriek_exact"]
theorem exactFunctor_degreewiseLowerShriek :
    exactFunctor
      (SheafOfModules.{max x u v w} (Stacks.SheafOfModules.Tensor.ringSheaf
        (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op n))).O))
      (SheafOfModules.{max x u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (degreewiseLowerShriek.{x, u, v, w} X K n) :=
  Stacks.Sites.ReducedLowerShriek.lowerShriek_exact.{max x v, max x u v w, max x u v w,
      max x u v, max x u v, v, u}
    (componentwiseTopology X.J (K.obj (op n))) X.J
    (⟨K.obj (op n), K.obj (op n), 𝟙 _⟩ :
      LocalizationSites.{x} X.C X.J).localizationFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (localizationReduction X.J (K.obj (op n)) _)

variable {n} {m : SimplexCategory}

/-- The relocalization functor followed by the localization functor of the target is the
localization functor of the source. -/
theorem relocalizationFunctor_comp_localizationFunctor {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {L M : FormalCoproduct.{x} C} (f : L ⟶ M) :
    (⟨L, M, f⟩ : LocalizationSites.{x} C J).relocalizationFunctor ⋙
        (⟨M, M, 𝟙 M⟩ : LocalizationSites.{x} C J).localizationFunctor =
      (⟨L, L, 𝟙 L⟩ : LocalizationSites.{x} C J).localizationFunctor :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ g => by cases g; rfl)

/-- The lower shriek `f_{φ!} : Mod(O_n) ⥤ Mod(O_m)` of the transition morphism of a simplex map
`φ : [m] ⟶ [n]`: a sheaf of `O_n`-modules is pushed forward as a presheaf of modules along the
componentwise relocalization functor `C/K_n ⥤ C/K_m` and sheafified. Its source is the category of
modules over `f_φ⁻¹O_m`, which is `O_n`. -/
def transitionLowerShriek (φ : m ⟶ n) :=
  Stacks.SheafOfModules.lowerShriek.{max x u v w, max x u v w, max x u v, max x u v,
      max x u v, max x u v}
    (componentwiseTopology X.J (K.obj (op n))) (componentwiseTopology X.J (K.obj (op m)))
    (⟨K.obj (op n), K.obj (op m), K.map φ.op⟩ :
      LocalizationSites.{x} X.C X.J).relocalizationFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op m))).O)

/-- The inverse image `f_φ^* = f_φ^{-1} : Mod(O_m) ⥤ Mod(O_n)` of the transition morphism of a
simplex map: restriction along the componentwise relocalization functor. -/
def transitionInverseImageModules (φ : m ⟶ n) :=
  Stacks.SheafOfModules.inverseImage.{max x u v w, max x u v w, max x u v, max x u v,
      max x u v, max x u v}
    (componentwiseTopology X.J (K.obj (op n))) (componentwiseTopology X.J (K.obj (op m)))
    (⟨K.obj (op n), K.obj (op m), K.map φ.op⟩ :
      LocalizationSites.{x} X.C X.J).relocalizationFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op m))).O)

/-- **Stacks 0D9W, the lower shriek of a transition morphism.** For a simplex map
`φ : [m] ⟶ [n]`, the inverse image `f_φ^*` of sheaves of modules along the transition morphism of
ringed topoi `f_φ : (Sh(C/K_n), O_n) ⟶ (Sh(C/K_m), O_m)` has a left adjoint
`f_{φ!} : Mod(O_n) ⥤ Mod(O_m)`.

Exactness of `f_{φ!}`, which the source asserts as well, is
`CategoryTheory.SemiRepresentable.Simplicial.exactFunctor_transitionLowerShriek`. -/
@[stacks 0D9W "transition_lower_shriek_adjunction"]
def transitionLowerShriekAdjunction (φ : m ⟶ n) :
    transitionLowerShriek.{x, u, v, w} X K φ ⊣ transitionInverseImageModules.{x, u, v, w} X K φ :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{max x u v w, max x u v w, max x u v, max x u v,
      max x u v, max x u v}
    (componentwiseTopology X.J (K.obj (op n))) (componentwiseTopology X.J (K.obj (op m)))
    (⟨K.obj (op n), K.obj (op m), K.map φ.op⟩ :
      LocalizationSites.{x} X.C X.J).relocalizationFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op m))).O)

/-- The localization functor of a semi-representable object is faithful: an arrow of the
componentwise localization is determined by its underlying arrow of the ambient site. -/
lemma localizationFunctor_faithful {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (L : FormalCoproduct.{x} C) :
    (⟨L, L, 𝟙 L⟩ : LocalizationSites.{x} C J).localizationFunctor.Faithful where
  map_injective := by
    rintro ⟨i, A⟩ ⟨j, B⟩ ⟨a⟩ ⟨b⟩ hab
    exact congrArg CategoryTheory.Sigma.SigmaHom.mk (Over.OverMorphism.ext hab)

/-- The relocalization functor of a morphism of semi-representable objects is faithful, its
composite with the localization functor of the target being the localization functor of the
source. -/
lemma relocalizationFunctor_faithful {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (S : LocalizationSites.{x} C J) :
    S.relocalizationFunctor.Faithful := by
  have := localizationFunctor_faithful J S.K
  exact Functor.Faithful.of_comp_eq
    (G := (⟨S.L, S.L, 𝟙 S.L⟩ : LocalizationSites.{x} C J).localizationFunctor)
    (relocalizationFunctor_comp_localizationFunctor J S.f)

/-- An identification of objects of a category is an isomorphism. -/
lemma isIso_eqToHom {A : Type u} [Category.{v} A] {Z Z' : A} (h : Z = Z') :
    IsIso (eqToHom h) :=
  ⟨eqToHom h.symm, by simp, by simp⟩

/-- A presheaf of rings sends an identification of objects to an isomorphism. -/
lemma isIso_map_eqToHom_op {A : Type u} [Category.{v} A] {Z Z' : A} (h : Z = Z')
    (P : Aᵒᵖ ⥤ RingCat.{r}) : IsIso (P.map (eqToHom h).op) := by
  have := isIso_eqToHom h
  infer_instance

/-- The index type of the connected components of the structured arrows out of an object `W` of
the degree-`m` componentwise localization along the relocalization functor: a component `i` of
`K_n` together with an arrow of the ambient site from the underlying object of `W` to `K_{n,i}`
exhibiting `W` as the image of the corresponding object of the slice site. -/
abbrev relocalizationFibre {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (S : LocalizationSites.{x} C J) (W : ComponentOver S.L) : Type (max x v) :=
  Σ (i : S.K.I) (h : W.2.left ⟶ S.K.obj i),
    PLift (W = (⟨S.f.f i, Over.mk (h ≫ S.f.φ i)⟩ : ComponentOver S.L))

/-- Two indices of `relocalizationFibre` agree as soon as their arrows of the ambient site do:
the identification of `W` they carry is a proposition. -/
lemma relocalizationFibre_ext {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {S : LocalizationSites.{x} C J} {W : ComponentOver S.L} {i : S.K.I}
    {h h' : W.2.left ⟶ S.K.obj i}
    (p : W = (⟨S.f.f i, Over.mk (h ≫ S.f.φ i)⟩ : ComponentOver S.L))
    (p' : W = (⟨S.f.f i, Over.mk (h' ≫ S.f.φ i)⟩ : ComponentOver S.L)) (hh : h = h') :
    (⟨i, h, ⟨p⟩⟩ : relocalizationFibre S W) = ⟨i, h', ⟨p'⟩⟩ := by
  subst hh
  rfl

/-- A structured arrow out of `W` along the relocalization functor exhibits `W` as the image of
the object of the slice site given by its underlying arrow of the ambient site. -/
lemma relocalizationFibre_obj_eq {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (S : LocalizationSites.{x} C J) {W : ComponentOver S.L}
    (s : StructuredArrow W S.relocalizationFunctor) :
    W = (⟨S.f.f s.right.1, Over.mk
      (((⟨S.L, S.L, 𝟙 S.L⟩ : LocalizationSites.{x} C J).localizationFunctor.map s.hom ≫
        s.right.2.hom) ≫ S.f.φ s.right.1)⟩ : ComponentOver S.L) := by
  obtain ⟨sl, ⟨i, Y⟩, sh⟩ := s
  obtain ⟨b⟩ := sh
  exact congrArg (Sigma.mk (S.f.f i))
    (congrArg Over.mk ((Over.w b).symm.trans (Category.assoc _ _ _).symm))

/-- **The reduction data of the relocalization functor of a morphism of semi-representable
objects.** A structured arrow `(c, W ⟶ f_φ(c))` out of `W` lies in the connected component
indexed by the component of `K_n` that `c` sits over together with the composite
`W.left ⟶ c.left ⟶ K_{n,i}`, and the terminal object of that component is the arrow that
identifies `W` with the image of the slice object of that composite. -/
noncomputable def relocalizationReduction {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (S : LocalizationSites.{x} C J)
    (O : (ComponentOver S.L)ᵒᵖ ⥤ RingCat.{r}) :
    Stacks.Sites.ReducedLowerShriek.Reduction.{max x v} S.relocalizationFunctor O where
  idx W := relocalizationFibre S W
  pt {W} t := StructuredArrow.mk (Y := (⟨t.1, Over.mk t.2.1⟩ : ComponentOver S.K))
    (eqToHom t.2.2.down)
  red {W} s := ⟨s.right.1,
    (⟨S.L, S.L, 𝟙 S.L⟩ : LocalizationSites.{x} C J).localizationFunctor.map s.hom ≫
      s.right.2.hom, ⟨relocalizationFibre_obj_eq S s⟩⟩
  lift {W} s := StructuredArrow.homMk
    (CategoryTheory.Sigma.SigmaHom.mk
      (Over.homMk ((⟨S.L, S.L, 𝟙 S.L⟩ :
        LocalizationSites.{x} C J).localizationFunctor.map s.hom)))
    (by
      apply (localizationFunctor_faithful J S.L).map_injective
      have hid : (⟨S.L, S.L, 𝟙 S.L⟩ : LocalizationSites.{x} C J).localizationFunctor.map
          (eqToHom (relocalizationFibre_obj_eq S s)) = 𝟙 _ :=
        (eqToHom_map _ _).trans (eqToHom_refl _ _)
      refine (CategoryTheory.Functor.map_comp _ _ _).trans ?_
      refine (congrArg (fun z => z ≫ _) hid).trans ?_
      exact Category.id_comp _)
  red_eq := by
    rintro W ⟨i, h, ⟨p⟩⟩ ⟨sl, ⟨j, Y⟩, sh⟩ ⟨gl, ⟨b⟩, gw⟩
    have hid : (⟨S.L, S.L, 𝟙 S.L⟩ : LocalizationSites.{x} C J).localizationFunctor.map
        (eqToHom p) = 𝟙 _ := (eqToHom_map _ _).trans (eqToHom_refl _ _)
    have hw0 : sh = eqToHom p ≫ S.relocalizationFunctor.map
        (CategoryTheory.Sigma.SigmaHom.mk b) := (Category.id_comp sh).symm.trans gw
    have hb : (⟨S.L, S.L, 𝟙 S.L⟩ : LocalizationSites.{x} C J).localizationFunctor.map sh =
        b.left := by
      refine (congrArg (fun z => (⟨S.L, S.L, 𝟙 S.L⟩ :
        LocalizationSites.{x} C J).localizationFunctor.map z) hw0).trans ?_
      refine (CategoryTheory.Functor.map_comp
        (⟨S.L, S.L, 𝟙 S.L⟩ : LocalizationSites.{x} C J).localizationFunctor
        (eqToHom p) (S.relocalizationFunctor.map
          (CategoryTheory.Sigma.SigmaHom.mk b))).trans ?_
      refine (congrArg (fun z => z ≫ _) hid).trans ?_
      exact Category.id_comp _
    refine relocalizationFibre_ext _ _ (Eq.trans ?_ (Over.w b))
    exact congrArg (fun z => z ≫ _) hb
  hom_ext := by
    intro W t s g g'
    have := isIso_eqToHom t.2.2.down
    rw [StructuredArrow.hom_eq_iff]
    exact (relocalizationFunctor_faithful S).map_injective <|
      (cancel_epi (eqToHom t.2.2.down)).1
        ((StructuredArrow.w g).trans (StructuredArrow.w g').symm)
  isIso_map {W} t := isIso_map_eqToHom_op t.2.2.down O

/-- **Stacks 0D9W, exactness of the lower shriek of a transition morphism.** For a simplex map
`φ : [m] ⟶ [n]`, the functor `f_{φ!} : Mod(O_n) ⥤ Mod(O_m)` left adjoint to the inverse image
`f_φ^*` is exact.

Right exactness is formal, `f_{φ!}` being a left adjoint. Left exactness is the direct-sum
formula: the sections of `f_{φ!}G` over an object `W` of the degree-`m` localization are the sum,
over the components `i` of `K_n` and the arrows `W.left ⟶ K_{n,i}` under `K(φ)`, of the sections
of `G` at the corresponding object of the slice site. -/
@[stacks 0D9W "transition_lower_shriek_exact"]
theorem exactFunctor_transitionLowerShriek (φ : m ⟶ n) :
    exactFunctor
      (SheafOfModules.{max x u v w} (Stacks.SheafOfModules.inverseImageRing
        (componentwiseTopology X.J (K.obj (op n))) (componentwiseTopology X.J (K.obj (op m)))
        (⟨K.obj (op n), K.obj (op m), K.map φ.op⟩ :
          LocalizationSites.{x} X.C X.J).relocalizationFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op m))).O)))
      (SheafOfModules.{max x u v w} (Stacks.SheafOfModules.Tensor.ringSheaf
        (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op m))).O))
      (transitionLowerShriek.{x, u, v, w} X K φ) :=
  Stacks.Sites.ReducedLowerShriek.lowerShriek_exact.{max x v, max x u v w, max x u v w,
      max x u v, max x u v, max x u v, max x u v}
    (componentwiseTopology X.J (K.obj (op n))) (componentwiseTopology X.J (K.obj (op m)))
    (⟨K.obj (op n), K.obj (op m), K.map φ.op⟩ :
      LocalizationSites.{x} X.C X.J).relocalizationFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (AlgebraicGeometry.RingedSite.localizationRingedTopos X (K.obj (op m))).O)
    (relocalizationReduction.{x, u, v, max x u v w} X.J
      (⟨K.obj (op n), K.obj (op m), K.map φ.op⟩ : LocalizationSites.{x} X.C X.J) _)

section ComponentInclusion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (L : SimplicialObject (FormalCoproduct.{x} C))

/-- The inclusion of the degree-`n` componentwise localization into the total localization site
is cocontinuous: a sieve covering the image of `(i, Y)` has, by definition of the total topology,
a covering sieve of vertical arrows over `Y.left`, and those vertical arrows are the images of a
covering sieve of `(i, Y)`. -/
instance componentInclusion_isCocontinuous (n : SimplexCategory) :
    (componentInclusion L n).IsCocontinuous
      (componentwiseTopology J (L.obj (op n))) (totalLocalizationTopology L J) where
  cover_lift := by
    rintro ⟨i, Y⟩ S hS
    change Sieve.overEquiv Y ((S.functorPullback (componentInclusion L n)).functorPullback
      (CategoryTheory.Sigma.incl
        (C := fun i : (L.obj (op n)).I => Over ((L.obj (op n)).obj i)) i)) ∈ J Y.left
    refine J.superset_covering ?_ hS
    intro W g hg
    rw [Sieve.overEquiv_iff]
    exact hg

/-- Pushing an arrow of the ambient site into a component of a formal coproduct commutes with
composition. -/
lemma fromIncl_comp {M : FormalCoproduct.{x} C} (i : M.I) {W V : C} (g : W ⟶ V)
    (p : V ⟶ M.obj i) :
    FormalCoproduct.Hom.fromIncl i (g ≫ p) =
      (FormalCoproduct.incl C).map g ≫ FormalCoproduct.Hom.fromIncl i p := rfl

variable {L}

/-- The first half of the factorisation of an arrow of the total site into an object of
simplicial degree `n`: the arrow whose underlying arrow of the ambient site is the identity and
which carries the whole simplicial part. -/
def fibreFactor {n : SimplexCategory} {i : (L.obj (op n)).I}
    {Y : Over ((L.obj (op n)).obj i)} {Z : TotalLocalization L}
    (h : Z ⟶ (componentInclusion L n).obj ⟨i, Y⟩) :
    Z ⟶ (componentInclusion L n).obj ⟨i, Over.mk (h.left ≫ Y.hom)⟩ where
  left := 𝟙 Z.left
  right := h.right
  w := by
    have hw : (FormalCoproduct.incl C).map h.left ≫
        FormalCoproduct.Hom.fromIncl i Y.hom = Z.hom ≫ L.map h.right := h.w
    change (FormalCoproduct.incl C).map (𝟙 Z.left) ≫
      FormalCoproduct.Hom.fromIncl i (h.left ≫ Y.hom) = Z.hom ≫ L.map h.right
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact (fromIncl_comp i h.left Y.hom).trans hw

/-- The second half of the factorisation: the arrow of the degree-`n` componentwise localization
whose image is vertical. -/
def fibreArrow {n : SimplexCategory} {i : (L.obj (op n)).I}
    {Y : Over ((L.obj (op n)).obj i)} {Z : TotalLocalization L}
    (h : Z ⟶ (componentInclusion L n).obj ⟨i, Y⟩) :
    (⟨i, Over.mk (h.left ≫ Y.hom)⟩ : ComponentOver (L.obj (op n))) ⟶ ⟨i, Y⟩ :=
  CategoryTheory.Sigma.SigmaHom.mk
    (C := fun i : (L.obj (op n)).I => Over ((L.obj (op n)).obj i))
    (Over.homMk h.left : Over.mk (h.left ≫ Y.hom) ⟶ Y)

/-- Every arrow of the total site into an object of simplicial degree `n` factors through the
image of an arrow of the degree-`n` componentwise localization. -/
lemma fibreFactor_comp {n : SimplexCategory} {i : (L.obj (op n)).I}
    {Y : Over ((L.obj (op n)).obj i)} {Z : TotalLocalization L}
    (h : Z ⟶ (componentInclusion L n).obj ⟨i, Y⟩) :
    fibreFactor h ≫ (componentInclusion L n).map (fibreArrow h) = h :=
  Comma.hom_ext _ _ (Category.id_comp h.left) (Category.comp_id h.right)

/-- Restriction along the component inclusion sends sheaves to sheaves: every arrow of the total
site into an object of simplicial degree `n` factors through a vertical arrow, so a compatible
family on a covering of `(i, Y)` determines one on the covering of its image by the arrows whose
underlying arrow of the ambient site covers. -/
instance componentInclusion_isContinuous (n : SimplexCategory) :
    (componentInclusion L n).IsContinuous
      (componentwiseTopology J (L.obj (op n))) (totalLocalizationTopology L J) where
  op_comp_isSheaf_of_types G := by
    rintro ⟨i, Y⟩ S hS x hx
    have hG := (isSheaf_iff_isSheaf_of_type (totalLocalizationTopology L J) G.obj).mp G.property
    have hx' := hx.to_sieveCompatible
    have hxeq : ∀ {B : ComponentOver (L.obj (op n))}
        (a b : B ⟶ (⟨i, Y⟩ : ComponentOver (L.obj (op n)))) (_ : a = b)
        (ha : S a) (hb : S b), x a ha = x b hb := by
      rintro B a b rfl ha hb
      rfl
    set Sv : Sieve ((componentInclusion L n).obj
        (⟨i, Y⟩ : ComponentOver (L.obj (op n)))).left :=
      Sieve.overEquiv Y (S.functorPullback (CategoryTheory.Sigma.incl
        (C := fun i : (L.obj (op n)).I => Over ((L.obj (op n)).obj i)) i)) with hSvdef
    have hmem : ∀ {Z : TotalLocalization L}
        (h : Z ⟶ (componentInclusion L n).obj (⟨i, Y⟩ : ComponentOver (L.obj (op n)))),
        Sv h.left → S (fibreArrow h) :=
      fun h hh => (Sieve.overEquiv_iff _ _).1 hh
    set T : Sieve ((componentInclusion L n).obj (⟨i, Y⟩ : ComponentOver (L.obj (op n)))) :=
      { arrows := fun _ h => Sv h.left
        downward_closed := fun hh g => Sv.downward_closed hh g.left } with hTdef
    have hT : T ∈ totalLocalizationTopology L J
        ((componentInclusion L n).obj (⟨i, Y⟩ : ComponentOver (L.obj (op n)))) := hS
    set y : Presieve.FamilyOfElements G.obj T.arrows :=
      fun _ h hh => G.obj.map (fibreFactor h).op (x (fibreArrow h) (hmem h hh)) with hydef
    have hy : y.Compatible := by
      refine (Presieve.compatible_iff_sieveCompatible _).2 ?_
      intro Z W h g hh
      have hgh : g ≫ fibreFactor h =
          fibreFactor (g ≫ h) ≫ (componentInclusion L n).map
            (CategoryTheory.Sigma.SigmaHom.mk
              (C := fun i : (L.obj (op n)).I => Over ((L.obj (op n)).obj i))
              (Over.homMk g.left (Category.assoc _ _ _).symm :
                Over.mk ((g ≫ h).left ≫ Y.hom) ⟶ Over.mk (h.left ≫ Y.hom))) := by
        apply Comma.hom_ext
        · change g.left ≫ 𝟙 Z.left = 𝟙 W.left ≫ g.left
          simp
        · change g.right ≫ h.right = (g.right ≫ h.right) ≫ 𝟙 _
          simp
      have hcomp : (CategoryTheory.Sigma.SigmaHom.mk
            (C := fun i : (L.obj (op n)).I => Over ((L.obj (op n)).obj i))
            (Over.homMk g.left (Category.assoc _ _ _).symm :
              Over.mk ((g ≫ h).left ≫ Y.hom) ⟶ Over.mk (h.left ≫ Y.hom))) ≫
            fibreArrow h = fibreArrow (g ≫ h) := by
        refine congrArg (CategoryTheory.Sigma.SigmaHom.mk
          (C := fun i : (L.obj (op n)).I => Over ((L.obj (op n)).obj i))) ?_
        exact Over.OverMorphism.ext rfl
      change G.obj.map (fibreFactor (g ≫ h)).op (x (fibreArrow (g ≫ h)) _) =
        G.obj.map g.op (G.obj.map (fibreFactor h).op (x (fibreArrow h) (hmem h hh)))
      rw [← CategoryTheory.Functor.map_comp_apply, ← CategoryTheory.op_comp, hgh,
        CategoryTheory.op_comp, CategoryTheory.Functor.map_comp_apply]
      refine congrArg (G.obj.map (fibreFactor (g ≫ h)).op) ?_
      exact (hxeq _ _ hcomp.symm _ _).trans (hx' (fibreArrow h) _ (hmem h hh))
    obtain ⟨t, ht, htuniq⟩ := hG _ hT y hy
    refine ⟨t, ?_, ?_⟩
    · rintro ⟨i', A⟩ f hf
      obtain ⟨f'⟩ := f
      set fS : (⟨i, A⟩ : ComponentOver (L.obj (op n))) ⟶ ⟨i, Y⟩ :=
        CategoryTheory.Sigma.SigmaHom.mk
          (C := fun i : (L.obj (op n)).I => Over ((L.obj (op n)).obj i)) f' with hfSdef
      have hvert : Sv ((componentInclusion L n).map fS).left :=
        Presieve.image_mem_functorPushforward (Over.forget _) _ hf
      set q : (⟨i, Over.mk (f'.left ≫ Y.hom)⟩ : ComponentOver (L.obj (op n))) ⟶ ⟨i, A⟩ :=
        CategoryTheory.Sigma.SigmaHom.mk
          (C := fun i : (L.obj (op n)).I => Over ((L.obj (op n)).obj i))
          (Over.homMk (𝟙 A.left) (by simp) :
            Over.mk (f'.left ≫ Y.hom) ⟶ A) with hqdef
      have hqf : q ≫ fS = fibreArrow ((componentInclusion L n).map fS) := by
        refine congrArg (CategoryTheory.Sigma.SigmaHom.mk
          (C := fun i : (L.obj (op n)).I => Over ((L.obj (op n)).obj i))) ?_
        exact Over.OverMorphism.ext (Category.id_comp _)
      have hid : fibreFactor ((componentInclusion L n).map fS) ≫
          (componentInclusion L n).map q = 𝟙 _ := by
        apply Comma.hom_ext
        · change 𝟙 A.left ≫ 𝟙 A.left = 𝟙 A.left
          simp
        · change 𝟙 (op n) ≫ 𝟙 (op n) = 𝟙 (op n)
          simp
      refine (ht _ hvert).trans ?_
      refine Eq.trans (congrArg
        (G.obj.map (fibreFactor ((componentInclusion L n).map fS)).op)
        ((hxeq _ _ hqf.symm (hmem _ hvert) _).trans (hx' fS q hf))) ?_
      calc G.obj.map (fibreFactor ((componentInclusion L n).map fS)).op
              (G.obj.map ((componentInclusion L n).map q).op (x fS hf))
          = G.obj.map ((fibreFactor ((componentInclusion L n).map fS) ≫
              (componentInclusion L n).map q).op) (x fS hf) :=
            (CategoryTheory.FunctorToTypes.map_comp_apply _ _ _ _).symm
        _ = G.obj.map (𝟙 ((componentInclusion L n).obj
              (⟨i, A⟩ : ComponentOver (L.obj (op n))))).op (x fS hf) :=
            congrArg (fun k : (componentInclusion L n).obj
                (⟨i, A⟩ : ComponentOver (L.obj (op n))) ⟶ (componentInclusion L n).obj
                (⟨i, A⟩ : ComponentOver (L.obj (op n))) =>
              G.obj.map k.op (x fS hf)) hid
        _ = x fS hf := CategoryTheory.FunctorToTypes.map_id_apply _ _
    · intro t' ht'
      refine htuniq t' fun Z h hh => ?_
      change G.obj.map h.op t' = G.obj.map (fibreFactor h).op (x (fibreArrow h) (hmem h hh))
      refine (congrArg (fun k : Z ⟶ _ => G.obj.map k.op t')
        (fibreFactor_comp h).symm).trans ?_
      change G.obj.map (fibreFactor h ≫ (componentInclusion L n).map (fibreArrow h)).op t' = _
      rw [CategoryTheory.op_comp, CategoryTheory.Functor.map_comp_apply]
      exact congrArg (G.obj.map (fibreFactor h).op) (ht' (fibreArrow h) (hmem h hh))

/-- The index type of the connected components of the structured arrows out of an object `Z` of
the total site along the inclusion of the degree-`n` component: a component of `L_n`, a simplex
map out of the degree of `Z`, and an arrow of the ambient site into that component, compatible
with the structure arrow of `Z`. -/
abbrev componentFibre (n : SimplexCategory) (Z : TotalLocalization L) : Type (max x v) :=
  Σ (i : (L.obj (op n)).I) (r : Z.right ⟶ op n) (h : Z.left ⟶ (L.obj (op n)).obj i),
    PLift (FormalCoproduct.Hom.fromIncl i h = Z.hom ≫ L.map r)

/-- Two indices of `componentFibre` agree as soon as their simplex maps and their arrows of the
ambient site do: the compatibility they carry is a proposition. -/
lemma componentFibre_ext {n : SimplexCategory} {Z : TotalLocalization L}
    {i : (L.obj (op n)).I} {r r' : Z.right ⟶ op n}
    {h h' : Z.left ⟶ (L.obj (op n)).obj i}
    (p : FormalCoproduct.Hom.fromIncl i h = Z.hom ≫ L.map r)
    (p' : FormalCoproduct.Hom.fromIncl i h' = Z.hom ≫ L.map r')
    (hr : r = r') (hh : h = h') :
    (⟨i, r, h, ⟨p⟩⟩ : componentFibre n Z) = ⟨i, r', h', ⟨p'⟩⟩ := by
  subst hr
  subst hh
  rfl

/-- The inclusion of a simplicial degree leaves the underlying arrow of the ambient site
alone. -/
lemma componentInclusion_map_left {n : SimplexCategory} {i : (L.obj (op n)).I}
    {U V : Over ((L.obj (op n)).obj i)} (a : U ⟶ V) :
    ((componentInclusion L n).map (CategoryTheory.Sigma.SigmaHom.mk a)).left = a.left := rfl

/-- The inclusion of a simplicial degree is vertical: it does not move the simplicial
degree. -/
lemma componentInclusion_map_right {n : SimplexCategory} {i : (L.obj (op n)).I}
    {U V : Over ((L.obj (op n)).obj i)} (a : U ⟶ V) :
    ((componentInclusion L n).map (CategoryTheory.Sigma.SigmaHom.mk a)).right = 𝟙 (op n) := rfl

end ComponentInclusion

section ComponentMorphism

variable (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
  (K : SimplicialObject (FormalCoproduct.{x} X.C)) (n : SimplexCategory)

/-- The degree-`n` component of the total ringed site, as a ringed topos: the componentwise
localization at `K_n`, with the structure sheaf `g_n⁻¹O`. -/
abbrev componentRingedTopos : AlgebraicGeometry.RingedTopos where
  C := ComponentOver (K.obj (op n))
  J := componentwiseTopology X.J (K.obj (op n))
  O := ((componentInclusion K n).sheafPushforwardContinuous CommRingCat.{max x u v w}
    (componentwiseTopology X.J (K.obj (op n))) (totalLocalizationTopology K X.J)).obj
      (pulledBackStructureSheaf X K)

/-- Right Kan extensions along the component inclusion exist at the universe of sections of the
total structure sheaf, both sites being small there. -/
theorem componentInclusion_hasPointwiseRightKanExtension
    (F : (ComponentOver (K.obj (op n)))ᵒᵖ ⥤ Type (max x u v w)) :
    (componentInclusion K n).op.HasPointwiseRightKanExtension F :=
  inferInstance

/-- The morphism of topoi underlying `g_n`: its inverse image is restriction along the component
inclusion and its direct image is the right Kan extension along it. -/
def componentMorphismOfTopoi :
    MorphismOfTopoi (componentRingedTopos.{x, u, v, w} X K n).Topos
      (AlgebraicGeometry.RingedSite.ringedTopos.{max u v x, v, w}
        (totalRingedSite.{x, u, v, max x u v w} X K)).Topos :=
  letI := componentInclusion_hasPointwiseRightKanExtension.{x, u, v, w} X K n
  { inverseImage := (componentInclusion K n).sheafPushforwardContinuous
      (Type (max x u v w)) (componentwiseTopology X.J (K.obj (op n)))
      (totalLocalizationTopology K X.J)
    pushforward := (componentInclusion K n).sheafPushforwardCocontinuous
      (Type (max x u v w)) (componentwiseTopology X.J (K.obj (op n)))
      (totalLocalizationTopology K X.J)
    adj := (componentInclusion K n).sheafAdjunctionCocontinuous
      (Type (max x u v w)) (componentwiseTopology X.J (K.obj (op n)))
      (totalLocalizationTopology K X.J)
    preservesFiniteLimits :=
      CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous
        (componentwiseTopology X.J (K.obj (op n))) (totalLocalizationTopology K X.J)
        (componentInclusion K n) (Type (max x u v w)) }

/-- The inverse image of the structure sheaf `O` of the total ringed site under `g_n` *is* the
structure sheaf `g_n⁻¹O` of the degree-`n` component: both are restriction of `O` along the
component inclusion, so the comparison is the canonical identity identification. -/
def componentInverseImageCommRingIso :
    (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
        (componentMorphismOfTopoi.{x, u, v, w} X K n)).obj
        (totalRingedSite.{x, u, v, max x u v w} X K).O ≅
      (componentRingedTopos.{x, u, v, w} X K n).O :=
  Stacks.Sheaves.ToposPullback.restrictionCommRingIso
    (componentwiseTopology X.J (K.obj (op n))) (totalLocalizationTopology K X.J)
    (componentInclusion K n) (pulledBackStructureSheaf X K)

/-- The structure map of `g_n` in direct-image form, `O ⟶ g_{n*}g_n⁻¹O`: the adjunct of
`componentInverseImageCommRingIso` under `g_n⁻¹ ⊣ g_{n*}` for sheaves of commutative rings. -/
def componentCommRingFsharpAdjoint :
    (totalRingedSite.{x, u, v, max x u v w} X K).O ⟶
      (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
        (componentMorphismOfTopoi.{x, u, v, w} X K n)).obj
        (componentRingedTopos.{x, u, v, w} X K n).O :=
  (Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
      (componentMorphismOfTopoi.{x, u, v, w} X K n)).homEquiv _ _
    (componentInverseImageCommRingIso.{x, u, v, w} X K n).hom

/-- **Stacks 0D9W, the morphism of a simplicial degree into the total ringed site.** For a
simplicial semi-representable object `K` of the underlying site of a ringed site `X`, the
degree-`n` componentwise localization is a ringed topos over the total ringed site by a morphism
of ringed topoi `g_n : (Sh(C/K_n), O_n) ⟶ (Sh((C/K)_total), O)`. -/
@[stacks 0D9W "component_morphism"]
def componentRingedMorphism :
    AlgebraicGeometry.RingedToposHom (componentRingedTopos.{x, u, v, w} X K n)
      (AlgebraicGeometry.RingedSite.ringedTopos.{max u v x, v, w}
        (totalRingedSite.{x, u, v, max x u v w} X K)) where
  toToposHom := componentMorphismOfTopoi.{x, u, v, w} X K n
  fSharp := componentCommRingFsharpAdjoint.{x, u, v, w} X K n

/-- The structure map of `g_n`, read in inverse-image form, is the identification
`componentInverseImageCommRingIso`. -/
theorem componentRingedMorphism_fSharpInverseImage :
    (componentRingedMorphism.{x, u, v, w} X K n).fSharpInverseImage =
      (componentInverseImageCommRingIso.{x, u, v, w} X K n).hom :=
  Equiv.symm_apply_apply _ _

/-- **Stacks 0D9W, flat component morphism.** The morphism of ringed topoi
`g_n : (Sh(C/K_n), O_n) ⟶ (Sh((C/K)_total), O)` is flat: its structure map in inverse-image form
is the identification of `g_n⁻¹O` with `O_n`, hence an isomorphism, and an isomorphism of sheaves
of commutative rings is flat. -/
@[stacks 0D9W "flat_component_morphism"]
theorem componentRingedMorphism_isFlat :
    Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat.{max x u v, max x u v,
        max x u v w, v, max u v x, max x u v w}
      (componentRingedMorphism.{x, u, v, w} X K n) := by
  refine AlgebraicGeometry.SheafOfModules.isFlatMapULift_of_isIso _ ?_
  rw [componentRingedMorphism_fSharpInverseImage.{x, u, v, w} X K n]
  exact (componentInverseImageCommRingIso.{x, u, v, w} X K n).isIso_hom

/-- `g_{n!} : Mod(g_n⁻¹O) ⥤ Mod(O)`. -/
def componentLowerShriek :
    SheafOfModules.{max x u v w} (Stacks.SheafOfModules.inverseImageRing
        (componentwiseTopology X.J (K.obj (op n))) (totalLocalizationTopology K X.J)
        (componentInclusion K n) (pulledBackRingSheaf X K)) ⥤
      SheafOfModules.{max x u v w} (pulledBackRingSheaf X K) :=
  Stacks.SheafOfModules.lowerShriek.{max x u v w, max x u v w, max x u v, max x u v,
      v, max u v x}
    (componentwiseTopology X.J (K.obj (op n))) (totalLocalizationTopology K X.J)
    (componentInclusion K n) (pulledBackRingSheaf X K)

/-- `g_n^* : Mod(O) ⥤ Mod(g_n⁻¹O)`. -/
def componentInverseImageModules :
    SheafOfModules.{max x u v w} (pulledBackRingSheaf X K) ⥤
      SheafOfModules.{max x u v w} (Stacks.SheafOfModules.inverseImageRing
        (componentwiseTopology X.J (K.obj (op n))) (totalLocalizationTopology K X.J)
        (componentInclusion K n) (pulledBackRingSheaf X K)) :=
  Stacks.SheafOfModules.inverseImage.{max x u v w, max x u v w, max x u v, max x u v,
      v, max u v x}
    (componentwiseTopology X.J (K.obj (op n))) (totalLocalizationTopology K X.J)
    (componentInclusion K n) (pulledBackRingSheaf X K)

/-- **Stacks 0D9W, the lower shriek of a component morphism.** The inverse image `g_n^*` of
sheaves of modules along `g_n` has a left adjoint `g_{n!} : Mod(O_n) ⥤ Mod(O)`.

Exactness of `g_{n!}`, which the source asserts as well, is
`CategoryTheory.SemiRepresentable.Simplicial.exactFunctor_componentLowerShriek`. -/
@[stacks 0D9W "component_lower_shriek_adjunction"]
def componentLowerShriekAdjunction :
    componentLowerShriek.{x, u, v, w} X K n ⊣ componentInverseImageModules.{x, u, v, w} X K n :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{max x u v w, max x u v w, max x u v, max x u v,
      v, max u v x}
    (componentwiseTopology X.J (K.obj (op n))) (totalLocalizationTopology K X.J)
    (componentInclusion K n) (pulledBackRingSheaf X K)

/-- The pulled-back sheaf of rings does not see an arrow of the total site whose underlying
arrow of the ambient site is an identity: its sections are those of `O_C` on the underlying
object. -/
lemma isIso_pulledBackRingSheaf_map_of_left_id {Z : TotalLocalization K}
    {d : SimplexCategoryᵒᵖ} {hw : (FormalCoproduct.incl X.C).obj Z.left ⟶ K.obj d}
    (φ : Z ⟶ (⟨Z.left, d, hw⟩ : TotalLocalization K)) (hφ : φ.left = 𝟙 Z.left) :
    IsIso ((pulledBackRingSheaf X K).obj.map φ.op) := by
  have h : (pulledBackRingSheaf X K).obj.map φ.op =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map ((𝟙 Z.left).op) := by
    rw [← hφ]
    rfl
  have h' : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map ((𝟙 Z.left).op) = 𝟙 _ :=
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map_id (op Z.left)
  rw [h, h']
  exact IsIso.id _

/-- **The reduction data of the inclusion of a simplicial degree into the total site.** A
structured arrow `(c, Z ⟶ g_n(c))` out of `Z` lies in the connected component indexed by the
component `i` of `K_n` that `c` sits over, the simplex map `Z.right ⟶ [n]` carried by its
structure arrow, and the composite `Z.left ⟶ c.left ⟶ K_{n,i}` of their underlying arrows; the
terminal object of that component is the arrow whose underlying arrow of the ambient site is the
identity. These are `fibreFactor` and `fibreArrow`, which is the same factorisation that makes
the inclusion continuous. -/
noncomputable def componentInclusionReduction :
    Stacks.Sites.ReducedLowerShriek.Reduction.{max x v} (componentInclusion K n)
      (pulledBackRingSheaf X K).obj where
  idx Z := componentFibre n Z
  pt {Z} t := StructuredArrow.mk
    (Y := (⟨t.1, Over.mk t.2.2.1⟩ : ComponentOver (K.obj (op n))))
    { left := 𝟙 Z.left
      right := t.2.1
      w := ((fromIncl_comp t.1 (𝟙 Z.left) t.2.2.1).symm.trans
        (congrArg (FormalCoproduct.Hom.fromIncl t.1) (Category.id_comp t.2.2.1))).trans
        t.2.2.2.down }
  red {Z} s := ⟨s.right.1, s.hom.right, s.hom.left ≫ s.right.2.hom,
    ⟨(fromIncl_comp s.right.1 s.hom.left s.right.2.hom).trans s.hom.w⟩⟩
  lift {Z} s := StructuredArrow.homMk (fibreArrow s.hom) (fibreFactor_comp s.hom)
  red_eq := by
    rintro Z ⟨i, r, h, ⟨hc⟩⟩ ⟨sl, ⟨j, Y⟩, ⟨shl, shr, shw⟩⟩ ⟨gl, ⟨a⟩, gw⟩
    have hl : shl = a.left :=
      ((Category.id_comp shl).symm.trans (congrArg CommaMorphism.left gw)).trans
        (Category.id_comp a.left)
    have hr : shr = r :=
      ((Category.id_comp shr).symm.trans (congrArg CommaMorphism.right gw)).trans
        (Category.comp_id r)
    refine componentFibre_ext _ _ hr (Eq.trans ?_ (Over.w a))
    exact congrArg (fun z => z ≫ _) hl
  hom_ext := by
    rintro Z ⟨i, r, h, ⟨hc⟩⟩ ⟨sl, ⟨j, Y⟩, ⟨shl, shr, shw⟩⟩ ⟨gl, ⟨a⟩, gw⟩ ⟨gl', ⟨a'⟩, gw'⟩
    have h1 : shl = a.left :=
      ((Category.id_comp shl).symm.trans (congrArg CommaMorphism.left gw)).trans
        (Category.id_comp a.left)
    have h2 : shl = a'.left :=
      ((Category.id_comp shl).symm.trans (congrArg CommaMorphism.left gw')).trans
        (Category.id_comp a'.left)
    rw [StructuredArrow.hom_eq_iff]
    exact congrArg CategoryTheory.Sigma.SigmaHom.mk
      (Over.OverMorphism.ext (h1.symm.trans h2))
  isIso_map {Z} _ := isIso_pulledBackRingSheaf_map_of_left_id.{x, u, v, w} X K _ rfl

/-- **Stacks 0D9W, exactness of the lower shriek of a component morphism.** The functor
`g_{n!} : Mod(O_n) ⥤ Mod(O)` left adjoint to the inverse image `g_n^*` is exact.

This is Stacks 0D74 for the `Comma`-category model of the total site: right exactness is formal,
`g_{n!}` being a left adjoint, and left exactness is the direct-sum formula, whose index set at
an object `Z` of the total site is `componentFibre` — a component of `K_n`, a simplex map
`Z.right ⟶ [n]` and an arrow of the ambient site into that component. The simplex maps are the
`φ : [n] ⟶ [m]` of the direct-sum formula of Tag 0D72. The flatness hypothesis of 0D74 is not
needed here: the structure sheaf of the total site is pulled back from the ambient site, so it
does not see the arrow along which a summand is taken. -/
@[stacks 0D9W "component_lower_shriek_exact"]
theorem exactFunctor_componentLowerShriek :
    exactFunctor
      (SheafOfModules.{max x u v w} (Stacks.SheafOfModules.inverseImageRing
        (componentwiseTopology X.J (K.obj (op n))) (totalLocalizationTopology K X.J)
        (componentInclusion K n) (pulledBackRingSheaf X K)))
      (SheafOfModules.{max x u v w} (pulledBackRingSheaf X K))
      (componentLowerShriek.{x, u, v, w} X K n) :=
  Stacks.Sites.ReducedLowerShriek.lowerShriek_exact.{max x v, max x u v w, max x u v w,
      max x u v, max x u v, v, max u v x}
    (componentwiseTopology X.J (K.obj (op n))) (totalLocalizationTopology K X.J)
    (componentInclusion K n) (pulledBackRingSheaf X K)
    (componentInclusionReduction.{x, u, v, w} X K n)

/-- The structure sheaf `g_n⁻¹O` of the degree-`n` component is the degree-`n` structure sheaf
`O_n` of Stacks 0D9U: the component inclusion followed by `j_total` is the localization functor
of `K_n`, so the two restrictions of `O_C` agree. -/
theorem componentInclusion_comp_totalLocalizationFunctor_eq :
    componentInclusion K n ⋙ totalLocalizationFunctor K =
      (⟨K.obj (op n), K.obj (op n), 𝟙 _⟩ :
        LocalizationSites.{x} X.C X.J).localizationFunctor :=
  componentInclusion_totalLocalizationFunctor K n

end ComponentMorphism

end CategoryTheory.SemiRepresentable.Simplicial
