module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPointPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# A totally acyclic sheaf of modules is acyclic for sections

Let `(C, J)` be a small site and `O` a sheaf of rings on it, and let `N` be a sheaf of
`O`-modules whose underlying abelian sheaf is totally acyclic in the sense of Stacks 072Y: its
cohomology over every sheaf of sets vanishes in positive degrees. Then `N` is right acyclic for

* `H^0(U, -)`, sections over an object `U` of the site — this is part (1) of Stacks 0731; and
* `F ↦ F(K) = Mor_{PSh(C)}(K, F)`, sections against a presheaf of sets `K` — part (2).

The source deduces part (2) from the definition of total acyclicity and part (1) from part (2).
The proof given here is instead the one used for part (4) in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/TotallyAcyclicDirectImage.lean`: the
totally acyclic modules form a class *adapted* to each of the two functors in the sense of
Stacks 05T8, and Stacks 05T8 says that every object of an adapted class is acyclic. Of the
three conditions of that criterion, the first two are the ones already established for part
(4) — every module embeds in a totally acyclic one because an injective module is totally
acyclic (`Stacks.Cohomology.isTotallyAcyclic_of_injective`), and total acyclicity passes from
the kernel and the middle term of a short exact sequence to its quotient
(`Stacks.Cohomology.isTotallyAcyclic_of_shortExact`). The third is that the functor carries
such a short exact sequence to a short exact sequence; both functors are left exact because
they are computed on the underlying sheaf of sets, where limits of sheaves of modules are
computed, and the quotient map stays epimorphic because the sequence *splits* after passing to
the underlying sheaves of sets (`Stacks.Cohomology.splitEpi_moduleSheafFunctor`), and a split
epimorphism of sheaves of sets stays split, hence surjective, under any functor to types.

## Main definitions

* `Stacks.Cohomology.morFromPresheaf`: `Mor_{PSh(C)}(K, -)` read on sheaves of sets.
* `Stacks.Cohomology.sectionsOverPresheaf`: the functor `F ↦ F(K)` of Stacks 079X, from sheaves
  of `O`-modules to abelian groups.

## Main results

* `Stacks.Cohomology.rightAcyclic_evaluation_of_isTotallyAcyclic`: **Stacks 0731, part (1)**.
* `Stacks.Cohomology.rightAcyclic_sectionsOverPresheaf_of_isTotallyAcyclic`: **Stacks 0731,
  part (2)**.

## Implementation notes

Part (1) is stated for Mathlib's `SheafOfModules.evaluation`, which is the module-valued
functor `F ↦ F(U)`: sections over `U` of a sheaf of `O`-modules are a module over `O(U)`.
Part (2) is stated with values in abelian groups, as the source states it ("the functor
`F ↦ F(K)` is a left exact functor `Mod(O) → Ab`" in Stacks 079X); `K` is allowed to be a
presheaf of sets, again as in the source.

The group structure on `F(K)` is the one transported along the finite-product-preserving
functor `morFromPresheaf J K` by `CategoryTheory.Sheaf.moduleObjAddCommGroup`, i.e. pointwise
addition of maps; no second copy of that construction is made here. `morFromPresheaf` is an
`abbrev` so that the transported structure and the computation rules for it stay visible to
`rw` and to instance search.

Left exactness of `sectionsOverPresheaf` is obtained from
`Stacks.Sheaves.RingedPoint.preservesFiniteLimits_moduleSheafFunctor`: composing with the
forgetful functor to types turns `sectionsOverPresheaf` into the underlying-sheaf-of-sets
functor followed by `morFromPresheaf J K`, and the forgetful functor on abelian groups
reflects finite limits. Additivity is then formal.

The two ringed structures have all of their universes equal, as in part (4) and in the source
of Stacks 072Z; the reason is recorded there.

Enough injectives for sheaves of modules, and injective resolutions of abelian sheaves, are not
hypotheses of these statements: both are proved, the first by Mathlib's
`SheafOfModules.instIsGrothendieckAbelian` and the second by `Sheaf.instIsGrothendieckAbelian`,
a Grothendieck abelian category having enough injectives. They are what the first condition of
Stacks 05T8 — every module embeds in a totally acyclic one — is obtained from, and they are also
what supplies the `HasRightDerivedFunctor` instance that stating `Functor.rightAcyclic` requires,
so the only hypothesis on the module here is the total acyclicity the source assumes.

## References

* [Stacks Project, Lemma 21.14.3 (Tag 0731)](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Section 21.13 (Tag 079X)](https://stacks.math.columbia.edu/tag/079X)
* [Stacks Project, Lemma 13.15.6 (Tag 05T8)](https://stacks.math.columbia.edu/tag/05T8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe x w v u

namespace Stacks.Cohomology

-- As in `TotallyAcyclicDirectImage.lean`: `CategoryTheory.Functor.rightAcyclic` mentions
-- `HasRightDerivedFunctor`, and the cheap instance coming from `EnoughInjectives` is given
-- precedence over the route that would try to prove termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Left exactness plus epimorphy is short exactness -/

/-- A left exact additive functor between abelian categories carries a short exact sequence to a
short exact sequence as soon as it keeps the quotient map epimorphic. -/
private lemma shortExact_map_of_epi {A : Type*} [Category A] [Abelian A]
    {B : Type*} [Category B] [Abelian B] (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E]
    {S : ShortComplex A} (hS : S.ShortExact) (hepi : Epi (E.map S.g)) :
    (S.map E).ShortExact := by
  obtain ⟨hexact, hmono⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp inferInstance S hS
  exact ShortComplex.ShortExact.mk' hexact hmono hepi

/-! ### The functor `F ↦ F(K)` of sections against a presheaf of sets -/

section SectionsOverPresheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w})

/-- `Mor_{PSh(C)}(K, -)` for `K` a presheaf of sets, read on sheaves of sets: a map out of `K`
into the presheaf of sets underlying a sheaf of sets. -/
abbrev morFromPresheaf (K : Cᵒᵖ ⥤ Type w) : Sheaf J (Type w) ⥤ Type (max u w) :=
  sheafToPresheaf J (Type w) ⋙ coyoneda.obj (op K)

/-- **The functor `F ↦ F(K)` of Stacks 079X.** For `K` a presheaf of sets on `C`, the group
`F(K) = Mor_{PSh(C)}(K, F)` of maps from `K` to the presheaf of sets underlying a sheaf of
`O`-modules `F`, with pointwise addition, functorially in `F`. -/
def sectionsOverPresheaf (K : Cᵒᵖ ⥤ Type w) :
    SheafOfModules.{w} R ⥤ AddCommGrpCat.{max u w} :=
  letI : ∀ G : SheafOfModules.{w} R,
      AddCommGroup ((morFromPresheaf J K).obj (Sheaf.moduleSheaf R G)) := fun G ↦
    Sheaf.moduleObjAddCommGroup R G (morFromPresheaf J K)
  { obj := fun G ↦ AddCommGrpCat.of ((morFromPresheaf J K).obj (Sheaf.moduleSheaf R G))
    map := fun {G G'} φ ↦ AddCommGrpCat.ofHom
      { toFun := (morFromPresheaf J K).map ((Sheaf.moduleSheafFunctor R).map φ)
        map_zero' := Sheaf.map_moduleSheafFunctor_map_zeroObj R
          (P := morFromPresheaf J K) (φ := φ)
        map_add' := Sheaf.map_moduleSheafFunctor_map_addObj R
          (P := morFromPresheaf J K) (φ := φ) }
    map_id := fun G ↦ by
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a ↦ ?_)
      have h : (Sheaf.moduleSheafFunctor R).map (𝟙 G) = 𝟙 _ :=
        CategoryTheory.Functor.map_id _ _
      change (morFromPresheaf J K).map ((Sheaf.moduleSheafFunctor R).map (𝟙 G)) a = a
      rw [h]
      exact (morFromPresheaf J K).map_id_apply _ a
    map_comp := fun {G₁ G₂ G₃} φ ψ ↦ by
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a ↦ ?_)
      have h : (Sheaf.moduleSheafFunctor R).map (φ ≫ ψ) =
          (Sheaf.moduleSheafFunctor R).map φ ≫ (Sheaf.moduleSheafFunctor R).map ψ :=
        CategoryTheory.Functor.map_comp _ _ _
      change (morFromPresheaf J K).map ((Sheaf.moduleSheafFunctor R).map (φ ≫ ψ)) a = _
      rw [h]
      exact (morFromPresheaf J K).map_comp_apply _ _ a }

omit [J.HasSheafCompose (forget RingCat)] in
/-- A map of sheaves of modules acts on `F(K)` by composition with the induced map of the
underlying sheaves of sets. -/
lemma sectionsOverPresheaf_map_apply (K : Cᵒᵖ ⥤ Type w) {G G' : SheafOfModules.{w} R}
    (φ : G ⟶ G') (a : (morFromPresheaf J K).obj (Sheaf.moduleSheaf R G)) :
    ((sectionsOverPresheaf J R K).map φ).hom a =
      (morFromPresheaf J K).map ((Sheaf.moduleSheafFunctor R).map φ) a := rfl

omit [J.HasSheafCompose (forget RingCat)] in
/-- The underlying sheaf of sets of the zero map of sheaves of modules is the zero section
composed with the map to the final sheaf of sets. -/
private lemma moduleSheafFunctor_map_zero_hom (G G' : SheafOfModules.{w} R) :
    (Sheaf.moduleSheafFunctor R).map (0 : G ⟶ G') =
      terminal.from (Sheaf.moduleSheaf R G) ≫ Sheaf.moduleZeroHom R G' := by
  refine Sheaf.hom_ext_sections (fun X s ↦ ?_)
  rw [Functor.map_comp_apply, Sheaf.sectionsFunctor_map_moduleZeroHom]
  rfl

/-- The functor `F ↦ F(K)` carries zero maps of sheaves of modules to zero homomorphisms. -/
instance preservesZeroMorphisms_sectionsOverPresheaf (K : Cᵒᵖ ⥤ Type w) :
    (sectionsOverPresheaf J R K).PreservesZeroMorphisms where
  map_zero G G' := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a ↦ ?_)
    exact (congrArg (fun m ↦ (morFromPresheaf J K).map m a)
        (moduleSheafFunctor_map_zero_hom J R G G')).trans
      (((morFromPresheaf J K).map_comp_apply _ _ a).trans
        (congrArg ((morFromPresheaf J K).map (Sheaf.moduleZeroHom R G'))
          ((morFromPresheaf J K).map_terminalFrom_apply a)))

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The functor `F ↦ F(K)` from sheaves of modules to abelian groups preserves finite limits. -/
instance preservesFiniteLimits_sectionsOverPresheaf (K : Cᵒᵖ ⥤ Type w) :
    PreservesFiniteLimits (sectionsOverPresheaf J R K) := by
  have := Stacks.Sheaves.RingedPoint.preservesFiniteLimits_moduleSheafFunctor J R
  have h : PreservesFiniteLimits (Sheaf.moduleSheafFunctor R ⋙ morFromPresheaf J K) :=
    comp_preservesFiniteLimits _ _
  have h' : PreservesFiniteLimits
      (sectionsOverPresheaf J R K ⋙ forget AddCommGrpCat.{max u w}) := h
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget AddCommGrpCat.{max u w})

/-- The functor `F ↦ F(K)` from sheaves of modules to abelian groups is additive. -/
instance additive_sectionsOverPresheaf (K : Cᵒᵖ ⥤ Type w) :
    (sectionsOverPresheaf J R K).Additive :=
  Functor.additive_of_preserves_binary_products _

end SectionsOverPresheaf

/-! ### Parts (1) and (2) of Stacks 0731 -/

section Sections

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{u})]
  [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  (R : Sheaf J RingCat.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} R)]

/-- Sections over an object of the site are additive: they are the evaluation of the underlying
presheaf of modules. -/
instance additive_evaluation (X : Cᵒᵖ) : (SheafOfModules.evaluation R X).Additive :=
  inferInstanceAs ((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj X).Additive)

omit [HasDerivedCategory (SheafOfModules R)] in
/-- The class of totally acyclic modules is adapted to the functor of sections over an object of
the site: the first two conditions are those of part (4), and the sections of the quotient map
stay surjective because the sequence splits on the underlying sheaves of sets. -/
private lemma adapted_evaluation (X : Cᵒᵖ)
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (h₁ : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj S.X₁))
    (h₂ : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj S.X₂)) :
    IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj S.X₃) ∧
      (S.map (SheafOfModules.evaluation R X)).ShortExact := by
  obtain ⟨hsplit⟩ := splitEpi_moduleSheafFunctor J R S hS h₁
  refine ⟨isTotallyAcyclic_of_shortExact J
      (hS.map_of_exact (SheafOfModules.toSheaf R)) h₁ h₂,
    shortExact_map_of_epi _ hS ?_⟩
  have hsurj : Function.Surjective
      ((Sheaf.sectionsFunctor J X).map ((Sheaf.moduleSheafFunctor R).map S.g)) :=
    (CategoryTheory.epi_iff_surjective _).1 (hsplit.map (Sheaf.sectionsFunctor J X)).epi
  rw [ModuleCat.epi_iff_surjective]
  exact hsurj

/-- **Stacks 0731, part (1).** A sheaf of modules whose underlying abelian sheaf is totally
acyclic is right acyclic for the functor `H^0(U, -)` of sections over an object of the site. -/
@[stacks 0731 "part (1): the functor H^0(U, -) of sections over an object of the site"]
theorem rightAcyclic_evaluation_of_isTotallyAcyclic (X : Cᵒᵖ)
    [HasDerivedCategory.{u} (ModuleCat.{u} (R.obj.obj X))]
    (N : SheafOfModules.{u} R)
    (hN : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj N)) :
    (SheafOfModules.evaluation R X).rightAcyclic N :=
  Functor.le_rightAcyclic (SheafOfModules.evaluation R X)
    (fun M ↦ IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj M))
    (fun M ↦ ⟨Injective.under M, isTotallyAcyclic_of_injective J R (Injective.under M),
      Injective.ι M, inferInstance⟩)
    (fun S hS h₁ h₂ ↦ adapted_evaluation J R X S hS h₁ h₂) N hN

omit [HasDerivedCategory (SheafOfModules R)] in
/-- The class of totally acyclic modules is adapted to the functor `F ↦ F(K)`: the first two
conditions are those of part (4), and `F(K)` of the quotient map stays surjective because the
sequence splits on the underlying sheaves of sets, where a split epimorphism stays split under
any functor to types. -/
private lemma adapted_sectionsOverPresheaf (K : Cᵒᵖ ⥤ Type u)
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (h₁ : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj S.X₁))
    (h₂ : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj S.X₂)) :
    IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj S.X₃) ∧
      (S.map (sectionsOverPresheaf J R K)).ShortExact := by
  obtain ⟨hsplit⟩ := splitEpi_moduleSheafFunctor J R S hS h₁
  refine ⟨isTotallyAcyclic_of_shortExact J
      (hS.map_of_exact (SheafOfModules.toSheaf R)) h₁ h₂,
    shortExact_map_of_epi _ hS ?_⟩
  have hsurj : Function.Surjective
      ((morFromPresheaf J K).map ((Sheaf.moduleSheafFunctor R).map S.g)) :=
    (CategoryTheory.epi_iff_surjective _).1 (hsplit.map (morFromPresheaf J K)).epi
  rw [AddCommGrpCat.epi_iff_surjective]
  exact hsurj

/-- **Stacks 0731, part (2).** A sheaf of modules whose underlying abelian sheaf is totally
acyclic is right acyclic for the functor `F ↦ F(K)` of sections against a presheaf of sets. -/
@[stacks 0731 "part (2): the functor F ↦ F(K) of sections against a presheaf of sets"]
theorem rightAcyclic_sectionsOverPresheaf_of_isTotallyAcyclic (K : Cᵒᵖ ⥤ Type u)
    [HasDerivedCategory.{u} AddCommGrpCat.{u}]
    (N : SheafOfModules.{u} R)
    (hN : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj N)) :
    (sectionsOverPresheaf J R K).rightAcyclic N :=
  Functor.le_rightAcyclic (sectionsOverPresheaf J R K)
    (fun M ↦ IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj M))
    (fun M ↦ ⟨Injective.under M, isTotallyAcyclic_of_injective J R (Injective.under M),
      Injective.ι M, inferInstance⟩)
    (fun S hS h₁ h₂ ↦ adapted_sectionsOverPresheaf J R K S hS h₁ h₂) N hN

end Sections

end Stacks.Cohomology

end
