module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ExactSections
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.Objects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.WeaklyContractible.CohomologyOverAWeaklyContractibleObject

/-!
# Testing families of weakly contractible objects

A *testing family* on a site is a collection of weakly contractible objects which covers every
object of the site. This file fixes such a family and proves that evaluation of abelian sheaves
on a member of the family is an exact functor.

Weak contractibility of an object `U` is a statement about sheaves of sets valued in the
morphism universe of the site, while the sheaves evaluated may be valued in an unrelated
universe. The main step is therefore a universe transfer: the same surjectivity statement
holds for sheaves of sets in any larger universe. It is proved by splitting the *small*
sheafified covering map produced by a weak contractibility witness and then extending the
lifted local sections along its sheafification unit in the common value universe.

## Main definitions

* `Stacks.WeaklyContractible.WeaklyContractibleTestingFamily`: a covering collection of weakly
  contractible objects of a site.

## Main results

* `Stacks.WeaklyContractible.surjective_sections_of_isWeaklyContractible`: weak contractibility
  tests sheaves of sets in any independently chosen value universe.
* `Stacks.WeaklyContractible.exact_sheafSections`: evaluation on a member of a testing family
  is exact, in any value universe.
* `Stacks.WeaklyContractible.exact_iff_exact_sections`: a short complex of sheaves of modules is
  exact exactly when its sections on every member of a testing family are exact.

## Implementation notes

The covering condition is `CategoryTheory.GrothendieckTopology.HasEnoughObjects`. The sheaf of
rings is not part of the family, since the family is a statement about the site alone; results
about sheaves of modules quantify over it separately.

## References

* [Stacks Project, Tag 0945](https://stacks.math.columbia.edu/tag/0945)
* [Stacks Project, Tag 0946](https://stacks.math.columbia.edu/tag/0946)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
* [Stacks Project, Tag 090K](https://stacks.math.columbia.edu/tag/090K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace Stacks.WeaklyContractible

/-- A covering collection of weakly contractible objects of a site. -/
structure WeaklyContractibleTestingFamily
    (C : Type u) [Category.{v} C] [Small.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type v)] where
  /-- The chosen collection of testing objects. -/
  B : ObjectProperty C
  /-- Every testing object is weakly contractible. -/
  isWeaklyContractible : ∀ {U : C}, B U → J.IsWeaklyContractible U
  /-- Every object of the site is covered by testing objects. -/
  hasEnoughObjects : J.HasEnoughObjects B

section UniverseTransfer

variable {C : Type u} [Category.{v} C]

/-- On a site with a `Type a`-small model, weak equivalences of presheaves of `Type a` are the
locally bijective morphisms. -/
theorem wEqualsLocallyBijective_of_small.{a, b, c} {C : Type c} [Category.{b} C]
    [Small.{a} C] [LocallySmall.{a} C]
    (J : GrothendieckTopology C) : J.WEqualsLocallyBijective (Type a) := by
  let : ((equivSmallModel.{a} C).inverse.inducedTopology J).WEqualsLocallyBijective (Type a) :=
    inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{b, _, c, _, a} J

/-- Raising the value universe preserves locally surjective morphisms of presheaves of sets. -/
private theorem isLocallySurjective_whiskerRight_uliftFunctor.{a, b}
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type b} (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J (Functor.whiskerRight f uliftFunctor.{a}) := by
  constructor
  intro U s
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J f s.down)
  rintro V g ⟨x, hx⟩
  exact ⟨ULift.up x, congrArg ULift.up hx⟩

/-- A small sheafification remains a sheafification after raising its value universe. -/
theorem w_whiskerRight_toSheafify_ulift [Small.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type v)] (P : Cᵒᵖ ⥤ Type v) :
    J.W (Functor.whiskerRight (toSheafify J P) uliftFunctor.{max u t}) := by
  let : J.WEqualsLocallyBijective (Type v) := wEqualsLocallyBijective_of_small.{v} J
  let η := toSheafify J P
  let η' := Functor.whiskerRight η uliftFunctor.{max u t}
  have : Presheaf.IsLocallySurjective J η' :=
    isLocallySurjective_whiskerRight_uliftFunctor J η
  have : Presheaf.IsLocallyInjective J η' := by
    constructor
    intro U x y hxy
    have he : η.app U x.down = η.app U y.down := congrArg ULift.down hxy
    refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J η x.down y.down he)
    intro V f hf
    exact congrArg ULift.up hf
  let : J.WEqualsLocallyBijective (Type (max u v t)) :=
    wEqualsLocallyBijective_of_small.{max u v t} J
  exact J.W_of_isLocallyBijective η'

/-- Weak contractibility of `U` is tested on sheaves of sets valued in the site's morphism
universe; this is the same surjectivity statement for sheaves valued in a larger universe. -/
theorem surjective_sections_of_isWeaklyContractible_large [Small.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type v)]
    (U : C) (hU : J.IsWeaklyContractible U)
    (F G : Sheaf J (Type (max u v t))) (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective φ) : Function.Surjective (φ.hom.app (op U)) := by
  intro s
  obtain ⟨I, V, f, hcov, hle⟩ :=
    Stacks.WeaklyContractible.exists_small_subcover J (Presheaf.imageSieve φ.hom s)
      (hφ.imageSieve_mem s)
  let L := (Functor.whiskeringRight Cᵒᵖ (Type v) (Type (max u v t))).obj
    uliftFunctor.{max u t}
  let P := ∐ fun i => yoneda.obj (V i)
  let a (i : I) := Presheaf.localPreimage φ.hom s (f i) (hle _ (Sieve.ofArrows_mk V f i))
  let aa : ∀ i : I, L.obj (yoneda.obj (V i)) ⟶ F.obj :=
    fun i => uliftYonedaEquiv.{max u t}.symm (a i)
  let α : L.obj P ⟶ F.obj :=
    (PreservesCoproduct.iso L (fun i => yoneda.obj (V i))).hom ≫ Sigma.desc aa
  let β : L.obj (yoneda.obj U) ⟶ G.obj := uliftYonedaEquiv.{max u t}.symm s
  have hα : α ≫ φ.hom = L.map (Stacks.WeaklyContractible.piPre V f) ≫ β := by
    apply (cancel_epi (PreservesCoproduct.iso L (fun i => yoneda.obj (V i))).inv).mp
    dsimp only [α]
    rw [← Category.assoc, Iso.inv_hom_id_assoc]
    apply Sigma.hom_ext
    intro i
    simp only [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc, ← L.map_comp_assoc,
      Stacks.WeaklyContractible.piPre, Sigma.ι_comp_desc]
    apply uliftYonedaEquiv.{max u t}.injective
    rw [Sigma.ι_comp_desc_assoc]
    change uliftYonedaEquiv.{max u t} (uliftYonedaEquiv.{max u t}.symm (a i) ≫ φ.hom) =
      uliftYonedaEquiv.{max u t} (uliftYoneda.map (f i) ≫ uliftYonedaEquiv.{max u t}.symm s)
    have hnat := uliftYonedaEquiv_naturality (uliftYonedaEquiv.{max u t}.symm s) (f i).op
    simp only [Equiv.apply_symm_apply, Quiver.Hom.unop_op] at hnat
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply, ← hnat]
    exact Presheaf.app_localPreimage φ.hom s (f i) (hle _ (Sieve.ofArrows_mk V f i))
  obtain ⟨τ, hτ⟩ := (w_whiskerRight_toSheafify_ulift.{t} J P F.obj F.property).surjective α
  obtain ⟨b, hb⟩ :=
    (w_whiskerRight_toSheafify_ulift.{t} J (yoneda.obj U) G.obj G.property).surjective β
  change L.map (toSheafify J P) ≫ τ = α at hτ
  change L.map (toSheafify J (yoneda.obj U)) ≫ b = β at hb
  have hglue : τ ≫ φ.hom = L.map (Stacks.WeaklyContractible.piSharp J V f).hom ≫ b := by
    apply (w_whiskerRight_toSheafify_ulift.{t} J P G.obj G.property).injective
    change L.map (toSheafify J P) ≫ (τ ≫ φ.hom) =
      L.map (toSheafify J P) ≫ (L.map (Stacks.WeaklyContractible.piSharp J V f).hom ≫ b)
    rw [← Category.assoc, hτ, hα, ← Category.assoc, ← L.map_comp,
      Stacks.WeaklyContractible.piSharp, ← toSheafify_naturality, L.map_comp, Category.assoc, hb]
  obtain ⟨σ, hσ⟩ := (J.isWeaklyContractible_iff_hasRightInverse U).mp hU I V f hcov
  let γ := L.map σ.hom ≫ τ
  have hγ : γ ≫ φ.hom = b := by
    have he : σ.hom ≫ (Stacks.WeaklyContractible.piSharp J V f).hom = 𝟙 _ :=
      congrArg (fun k => k.hom) hσ
    dsimp [γ]
    rw [Category.assoc, hglue, ← Category.assoc, ← L.map_comp, he, L.map_id, Category.id_comp]
  have hfin : (L.map (toSheafify J (yoneda.obj U)) ≫ γ) ≫ φ.hom = β := by
    rw [Category.assoc, hγ, hb]
  refine ⟨uliftYonedaEquiv.{max u t} (L.map (toSheafify J (yoneda.obj U)) ≫ γ), ?_⟩
  rw [← uliftYonedaEquiv_comp]
  exact (congrArg uliftYonedaEquiv.{max u t} hfin).trans
    (uliftYonedaEquiv.{max u t}.apply_symm_apply s)

/-- Weak contractibility tests sheaves in any independently chosen value universe. -/
theorem surjective_sections_of_isWeaklyContractible [Small.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type v)]
    (U : C) (hU : J.IsWeaklyContractible U)
    (F G : Sheaf J (Type t)) (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective φ) : Function.Surjective (φ.hom.app (op U)) := by
  let L := sheafCompose J uliftFunctor.{max u v, t}
  have hL : Sheaf.IsLocallySurjective (L.map φ) :=
    isLocallySurjective_whiskerRight_uliftFunctor J φ.hom
  intro s
  obtain ⟨x, hx⟩ := surjective_sections_of_isWeaklyContractible_large.{t}
    J U hU (L.obj F) (L.obj G) (L.map φ) hL (ULift.up s)
  exact ⟨x.down, congrArg ULift.down hx⟩

end UniverseTransfer

/-- Evaluation on a member of a weakly contractible testing family is exact, in any
value universe. -/
theorem exact_sheafSections
    {C : Type u} [Category.{v} C] [Small.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type v)]
    [HasSheafify J AddCommGrpCat.{t}]
    (h : WeaklyContractibleTestingFamily C J) (U : C) (hU : h.B U) :
    exactFunctor (Sheaf J AddCommGrpCat.{t}) AddCommGrpCat.{t}
      ((sheafSections J AddCommGrpCat.{t}).obj (op U)) :=
  exact_sheafSections_of_isWeaklyContractible.{t} J U
    (surjective_sections_of_isWeaklyContractible J U (h.isWeaklyContractible hU))

/-- A short complex of sheaves of modules is exact exactly when its sections on every
member of a weakly contractible testing family are exact. The module universe is
independent of both the site and the sheaf of rings. -/
theorem exact_iff_exact_sections
    {C : Type u} [Category.{v} C] [Small.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type v)]
    [HasSheafify J AddCommGrpCat.{t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
    (h : WeaklyContractibleTestingFamily C J) (O : Sheaf J RingCat.{w})
    (S : ShortComplex (SheafOfModules.{t} O)) :
    S.Exact ↔ ∀ {U : C}, h.B U →
      Function.Exact (S.f.val.app (op U)) (S.g.val.app (op U)) :=
  let h' : WeaklyContractibleObjectsSituation.{w, v, u, t} C J :=
    { B := h.B
      isWeaklyContractible := fun _ hU =>
        surjective_sections_of_isWeaklyContractible J _ (h.isWeaklyContractible hU)
      hasEnoughObjects := h.hasEnoughObjects
      O := O }
  exact_iff_exact_sections_of_weaklyContractibleObjectsSituation J h' S

end Stacks.WeaklyContractible

end
