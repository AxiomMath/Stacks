module

public import StacksFrontier.AlgebraicGeometry.Perfect.LiftingComplexes.TwoOpenStep
import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a map from a perfect complex: the general case

Let `X` be a quasi-compact quasi-separated scheme, `U ⊆ X` a quasi-compact open, `T ⊆ X` a closed
subset whose complement is retrocompact in `X`, and `E` an object of `D_QCoh(𝒪_X)`. Every map
`α : P ⟶ E|_U` out of a perfect object `P` of `D(𝒪_U)` whose cohomology is supported on `T ∩ U`
is, up to a direct summand, the restriction of a map `β : R ⟶ E` out of a perfect object `R` of
`D(𝒪_X)` whose cohomology is supported on `T`. This is [Stacks, Tag 09IM].

The source covers `X` by `U` and finitely many affine opens `V₁, …, V_m` and inducts on `m`. That
induction is `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_list`, run over a list of
affine opens; its single step is the glueing step
`Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_cover_spec`, and its base case `m = 0`
is the same glueing step with the second open taken to be the *empty* affine, which is how the
transport across a surjective open immersion is obtained without any separate equivalence.

## Main results

* `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift`: **[Stacks, Tag 09IM]**.
* `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_list`: the induction over an affine
  cover.
* `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_step`: one step of that induction.
* `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_range_eq_univ`: the base case.
* `Stacks.Perfect.LiftingComplexes.restrictCompIso`: the comparison of the restriction along a
  composite of open immersions with the two restrictions.
* `Stacks.Perfect.LiftingComplexes.isCompact_preimage`: the preimage of a set under an open
  immersion is quasi-compact as soon as the part of the set inside the image is.

## Implementation notes

**The induction is on a list rather than through [Stacks, Tag 08DR].** The induction principle of
08DR passes from `W`, `V` and `W ⊓ V` to `W ⊔ V`; the induction the source runs here is the plain
one on the number of affine opens, and running it directly is what keeps the ambient scheme of the
*conclusion* equal to `X` at every stage. The first open is therefore carried by an arbitrary open
immersion `g : Y ⟶ X` rather than as a subscheme, and `Y` is universally quantified inside the
induction: the step replaces `g` by the inclusion of `g.opensRange ⊔ V`, so the source of the open
immersion changes while the target does not.

**One comparison of restrictions per step, and no coherence between them.** The step restricts `E`
to `g.opensRange ⊔ V`, which forces one comparison
`Stacks.Perfect.LiftingComplexes.restrictCompIso` between `(·)|_Y` and the composite
`(·)|_{g.opensRange ⊔ V}` followed by `(·)|_Y`. It is used twice -- once to transport `α` into the
glueing step and once to transport the glueing step's output back -- and the two uses cancel, so
no associativity coherence of the comparisons is needed. That is the reason for inducting with the
conclusion on `X`: an induction whose conclusion lived over a growing open would chain the
comparisons and require their pentagon.

**Retrocompactness enters only through the affine opens of the cover.** The induction uses the
hypothesis once per step, for the affine open being added; the statement keeps it in the form the
source gives it, as a condition on every quasi-compact open.

## References

* [Stacks Project, Lemma 36.13.11 (Tag 09IM)](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Lemma 20.47.1 (Tag 08DG)](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Lemma 30.3.2 (Tag 08DR)](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Duality.OpenImmersion (derivedRestrict)
open Stacks.SchemeCohomology (ringedSpace hom)

namespace Stacks.Perfect.LiftingComplexes

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The comparison of the restriction along a composite with the two restrictions.** -/
def restrictCompIso {X X' Y : Scheme.{u}} (g' : Y ⟶ X') (h : X' ⟶ X) (g : Y ⟶ X)
    [IsOpenImmersion g'] [IsOpenImmersion h] [IsOpenImmersion g] (hfac : g' ≫ h = g) :
    derivedRestrict h ⋙ derivedRestrict g' ≅ derivedRestrict g :=
  Functor.mapDerivedCategoryCompIsoOfCompIso
    ((Scheme.Modules.restrictFunctorComp g' h).symm ≪≫ Scheme.Modules.restrictFunctorCongr hfac)

/-- **The preimage of a set under an open immersion is quasi-compact as soon as the part of the
set inside the image is.** -/
theorem isCompact_preimage {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (S : Set X)
    (hS : IsCompact (S ∩ Set.range ⇑f.base)) : IsCompact (⇑f.base ⁻¹' S) := by
  rwa [(Scheme.Hom.isOpenEmbedding f).isEmbedding.isCompact_iff,
    Set.image_preimage_eq_inter_range]

/-- **Transport along an open immersion whose image is everything.** This is the glueing step of
[Stacks, Tag 09IM] with the second open taken to be the empty affine: no glueing happens, and the
statement is simply carried across the isomorphism `g`. -/
theorem exists_isPerfect_lift_of_range_eq_univ {X Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (hsurj : ∀ x : X, x ∈ Set.range ⇑g.base) (T : Set X) (hT : IsClosed T)
    (E : DerivedCategory X.Modules)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := X.ringCatSheaf) E)
    (P : DerivedCategory Y.Modules) (hP : IsPerfect (X := ringedSpace Y) P)
    (hPT : CohomologySupportedOn Y.ringCatSheaf (⇑g.base ⁻¹' T) P)
    (α : P ⟶ (derivedRestrict g).obj E) :
    ∃ (R : DerivedCategory X.Modules) (β : R ⟶ E),
      IsPerfect (X := ringedSpace X) R ∧
      CohomologySupportedOn X.ringCatSheaf T R ∧
      ∃ (i : P ⟶ (derivedRestrict g).obj R) (p : (derivedRestrict g).obj R ⟶ P),
        i ≫ p = 𝟙 P ∧ i ≫ (derivedRestrict g).map β = α := by
  have hbot : IsAffineOpen (⊥ : X.Opens) := isAffineOpen_bot X
  have hrange : Set.range ⇑hbot.fromSpec.base = (∅ : Set X) := by
    rw [hbot.range_fromSpec]
    simp
  have hempty : IsEmpty ↥(Spec Γ(X, (⊥ : X.Opens))) := Set.range_eq_empty_iff.mp hrange
  have hall : ∀ s : Set ↥(Spec Γ(X, (⊥ : X.Opens))), IsCompact s := by
    intro s
    rw [Set.eq_empty_of_isEmpty s]
    exact isCompact_empty
  obtain ⟨R, β, hRp, hRT, -, hsplit⟩ := exists_isPerfect_lift_of_cover_spec g hbot.fromSpec
    (fun x => Or.inl (hsurj x)) T hT (hall _) (hall _) E hE P hP hPT α
  exact ⟨R, β, hRp, hRT, hsplit⟩

/-- **Composing two retracts across a natural isomorphism `F ⋙ G ≅ H`.** -/
private theorem retract_comp_of_iso {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C} (e : F ⋙ G ≅ H) {P : C} {E R : A} {R₁ : B}
    {α : P ⟶ H.obj E} {β₁ : R₁ ⟶ F.obj E} {β : R ⟶ E} {i₁ : P ⟶ G.obj R₁}
    {p₁ : G.obj R₁ ⟶ P} (hip₁ : i₁ ≫ p₁ = 𝟙 P) (hiβ₁ : i₁ ≫ G.map β₁ = α ≫ e.inv.app E)
    {i₂ : R₁ ⟶ F.obj R} {p₂ : F.obj R ⟶ R₁} (hip₂ : i₂ ≫ p₂ = 𝟙 R₁)
    (hiβ₂ : i₂ ≫ F.map β = β₁) :
    (i₁ ≫ G.map i₂ ≫ e.hom.app R) ≫ e.inv.app R ≫ G.map p₂ ≫ p₁ = 𝟙 P ∧
      (i₁ ≫ G.map i₂ ≫ e.hom.app R) ≫ H.map β = α := by
  refine ⟨?_, ?_⟩
  · simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc (G.map i₂), ← Functor.map_comp, hip₂, CategoryTheory.Functor.map_id,
      Category.id_comp]
    exact hip₁
  · simp only [Category.assoc]
    rw [← e.hom.naturality β]
    simp only [Functor.comp_map]
    rw [← Category.assoc (G.map i₂), ← Functor.map_comp, hiβ₂, ← Category.assoc, hiβ₁,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- **A morphism into `X` with image inside an open `W` factors through `W` by an open
immersion.** -/
private theorem exists_isOpenImmersion_factor {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (W : X.Opens) (h : Set.range ⇑g.base ⊆ Set.range ⇑W.ι.base) :
    ∃ (g₀ : Y ⟶ W.toScheme) (_ : IsOpenImmersion g₀), g₀ ≫ W.ι = g := by
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : Y ⟶ W.toScheme, g₀ ≫ W.ι = g :=
    ⟨IsOpenImmersion.lift _ _ h, IsOpenImmersion.lift_fac _ _ h⟩
  have : IsOpenImmersion (g₀ ≫ W.ι) := by
    rw [hg₀]
    infer_instance
  exact ⟨g₀, IsOpenImmersion.of_comp g₀ W.ι, hg₀⟩

/-- **The underlying map of a composite of morphisms of schemes is the composite of the maps.** -/
private theorem comp_base_apply_eq {X Y Z : Scheme.{u}} {f : Y ⟶ Z} {h : Z ⟶ X} {g : Y ⟶ X}
    (hfac : f ≫ h = g) (y : Y) : h.base (f.base y) = g.base y := by
  subst hfac
  rfl

/-- **Points of an open covered by two morphisms lie in the range of one of their lifts.** -/
private theorem mem_range_or_mem_range_of_comp_eq {X Y Z : Scheme.{u}} {W : X.Opens} {g : Y ⟶ X}
    {f : Z ⟶ X} (hcov : (W : Set X) ⊆ Set.range ⇑g.base ∪ Set.range ⇑f.base)
    {g₀ : Y ⟶ W.toScheme} {f₀ : Z ⟶ W.toScheme} (hg₀ : g₀ ≫ W.ι = g) (hf₀ : f₀ ≫ W.ι = f)
    (x : W.toScheme) : x ∈ Set.range ⇑g₀.base ∨ x ∈ Set.range ⇑f₀.base := by
  have hinj : Function.Injective ⇑W.ι.base := (Scheme.Hom.isOpenEmbedding W.ι).injective
  have hxι : ⇑W.ι.base x = x.1 := rfl
  rcases hcov x.2 with ⟨y, hy⟩ | ⟨z, hz⟩
  · exact Or.inl ⟨y, hinj (by rw [comp_base_apply_eq hg₀, hxι, hy])⟩
  · exact Or.inr ⟨z, hinj (by rw [comp_base_apply_eq hf₀, hxι, hz])⟩

/-- **The glueing step of [Stacks, Tag 09IM] over `g.opensRange ⊔ V`.** A map out of a perfect
object on the source of `g`, supported on the preimage of `T`, comes up to a direct summand from a
perfect object on `g.opensRange ⊔ V` supported on the preimage of `T`. -/
private theorem exists_isPerfect_lift_sup {X Y : Scheme.{u}} [QuasiSeparatedSpace X] (T : Set X)
    (hT : IsClosed T) (E : DerivedCategory X.Modules)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := X.ringCatSheaf) E) (g : Y ⟶ X) [IsOpenImmersion g]
    (hgc : IsCompact (Set.range ⇑g.base)) (V : X.Opens) (hV : IsAffineOpen V)
    (hTV : IsCompact ((V : Set X) ∩ Tᶜ)) (g₀ : Y ⟶ (g.opensRange ⊔ V : X.Opens).toScheme)
    [IsOpenImmersion g₀] (hg₀ : g₀ ≫ (g.opensRange ⊔ V : X.Opens).ι = g)
    (P : DerivedCategory Y.Modules) (hP : IsPerfect (X := ringedSpace Y) P)
    (hPT : CohomologySupportedOn Y.ringCatSheaf (⇑g.base ⁻¹' T) P)
    (α : P ⟶ (derivedRestrict g₀).obj ((derivedRestrict (g.opensRange ⊔ V : X.Opens).ι).obj E)) :
    ∃ (R₁ : DerivedCategory (g.opensRange ⊔ V : X.Opens).toScheme.Modules)
      (β₁ : R₁ ⟶ (derivedRestrict (g.opensRange ⊔ V : X.Opens).ι).obj E),
      IsPerfect (X := ringedSpace (g.opensRange ⊔ V : X.Opens).toScheme) R₁ ∧
      CohomologySupportedOn (g.opensRange ⊔ V : X.Opens).toScheme.ringCatSheaf
        (⇑(g.opensRange ⊔ V : X.Opens).ι.base ⁻¹' T) R₁ ∧
      ∃ (i : P ⟶ (derivedRestrict g₀).obj R₁) (p : (derivedRestrict g₀).obj R₁ ⟶ P),
        i ≫ p = 𝟙 P ∧ i ≫ (derivedRestrict g₀).map β₁ = α := by
  classical
  have hinj : Function.Injective ⇑(g.opensRange ⊔ V : X.Opens).ι.base :=
    (Scheme.Hom.isOpenEmbedding (g.opensRange ⊔ V : X.Opens).ι).injective
  have hfsub : Set.range ⇑hV.fromSpec.base ⊆
      Set.range ⇑(g.opensRange ⊔ V : X.Opens).ι.base := by
    rw [Scheme.Opens.range_ι, hV.range_fromSpec]
    exact le_sup_right
  obtain ⟨f₀, _, hf₀⟩ := exists_isOpenImmersion_factor hV.fromSpec _ hfsub
  have hcov : ((g.opensRange ⊔ V : X.Opens) : Set X) ⊆
      Set.range ⇑g.base ∪ Set.range ⇑hV.fromSpec.base := by
    rw [hV.range_fromSpec]
    exact fun x hx => Opens.mem_sup.1 hx
  have hcover := mem_range_or_mem_range_of_comp_eq hcov hg₀ hf₀
  have hTsets : ⇑f₀.base ⁻¹' (⇑(g.opensRange ⊔ V : X.Opens).ι.base ⁻¹' T) =
      ⇑hV.fromSpec.base ⁻¹' T := by
    ext z
    show ⇑(g.opensRange ⊔ V : X.Opens).ι.base (⇑f₀.base z) ∈ T ↔ ⇑hV.fromSpec.base z ∈ T
    rw [comp_base_apply_eq hf₀]
  have hTf : IsCompact
      ((⇑f₀.base ⁻¹' (⇑(g.opensRange ⊔ V : X.Opens).ι.base ⁻¹' T))ᶜ) := by
    rw [hTsets, ← Set.preimage_compl]
    exact isCompact_preimage hV.fromSpec Tᶜ (by rwa [hV.range_fromSpec, Set.inter_comm])
  have hWsets : ((f₀ ⁻¹ᵁ g₀.opensRange : (Spec Γ(X, V)).Opens) : Set (Spec Γ(X, V))) =
      ⇑hV.fromSpec.base ⁻¹' Set.range ⇑g.base := by
    ext z
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [← comp_base_apply_eq hg₀, hy, comp_base_apply_eq hf₀]⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hinj (by rw [comp_base_apply_eq hg₀, hy, comp_base_apply_eq hf₀])⟩
  have hW : IsCompact
      ((f₀ ⁻¹ᵁ g₀.opensRange : (Spec Γ(X, V)).Opens) : Set (Spec Γ(X, V))) := by
    rw [hWsets]
    refine isCompact_preimage hV.fromSpec (Set.range ⇑g.base) ?_
    rw [hV.range_fromSpec]
    exact hgc.inter_of_isOpen hV.isCompact (Scheme.Hom.isOpenEmbedding g).isOpen_range V.isOpen
  have hPsets : ⇑g₀.base ⁻¹' (⇑(g.opensRange ⊔ V : X.Opens).ι.base ⁻¹' T) =
      ⇑g.base ⁻¹' T := by
    ext y
    show ⇑(g.opensRange ⊔ V : X.Opens).ι.base (⇑g₀.base y) ∈ T ↔ ⇑g.base y ∈ T
    rw [comp_base_apply_eq hg₀]
  obtain ⟨R₁, β₁, hR₁p, hR₁T, -, hsplit⟩ :=
    exists_isPerfect_lift_of_cover_spec g₀ f₀ hcover
      (⇑(g.opensRange ⊔ V : X.Opens).ι.base ⁻¹' T)
      (hT.preimage (g.opensRange ⊔ V : X.Opens).ι.base.hom.continuous) hTf hW
      ((derivedRestrict (g.opensRange ⊔ V : X.Opens).ι).obj E)
      (Stacks.DerivedQCoh.isDQCoh_derivedRestrict _ E hE) P hP (hPsets ▸ hPT) α
  exact ⟨R₁, β₁, hR₁p, hR₁T, hsplit⟩

/-- **One step of the induction of [Stacks, Tag 09IM] over an affine cover.** One affine open `V`
is added to the image of `g`; the glueing step produces an object over `g.opensRange ⊔ V`, and the
induction hypothesis -- stated here as the hypothesis `IH`, for that one open -- carries it the
rest of the way to `X`. -/
theorem exists_isPerfect_lift_step {X Y : Scheme.{u}} [QuasiSeparatedSpace X] (T : Set X)
    (hT : IsClosed T) (E : DerivedCategory X.Modules)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := X.ringCatSheaf) E) (g : Y ⟶ X) [IsOpenImmersion g]
    (hgc : IsCompact (Set.range ⇑g.base)) (V : X.Opens) (hV : IsAffineOpen V)
    (hTV : IsCompact ((V : Set X) ∩ Tᶜ)) (P : DerivedCategory Y.Modules)
    (hP : IsPerfect (X := ringedSpace Y) P)
    (hPT : CohomologySupportedOn Y.ringCatSheaf (⇑g.base ⁻¹' T) P)
    (α : P ⟶ (derivedRestrict g).obj E)
    (IH : ∀ (R₁ : DerivedCategory (g.opensRange ⊔ V : X.Opens).toScheme.Modules),
      IsPerfect (X := ringedSpace (g.opensRange ⊔ V : X.Opens).toScheme) R₁ →
      CohomologySupportedOn (g.opensRange ⊔ V : X.Opens).toScheme.ringCatSheaf
        (⇑(g.opensRange ⊔ V : X.Opens).ι.base ⁻¹' T) R₁ →
      ∀ β₁ : R₁ ⟶ (derivedRestrict (g.opensRange ⊔ V : X.Opens).ι).obj E,
      ∃ (R : DerivedCategory X.Modules) (β : R ⟶ E),
        IsPerfect (X := ringedSpace X) R ∧ CohomologySupportedOn X.ringCatSheaf T R ∧
        ∃ (i : R₁ ⟶ (derivedRestrict (g.opensRange ⊔ V : X.Opens).ι).obj R)
          (p : (derivedRestrict (g.opensRange ⊔ V : X.Opens).ι).obj R ⟶ R₁),
          i ≫ p = 𝟙 R₁ ∧
          i ≫ (derivedRestrict (g.opensRange ⊔ V : X.Opens).ι).map β = β₁) :
    ∃ (R : DerivedCategory X.Modules) (β : R ⟶ E),
      IsPerfect (X := ringedSpace X) R ∧
      CohomologySupportedOn X.ringCatSheaf T R ∧
      ∃ (i : P ⟶ (derivedRestrict g).obj R) (p : (derivedRestrict g).obj R ⟶ P),
        i ≫ p = 𝟙 P ∧ i ≫ (derivedRestrict g).map β = α := by
  have hgsub : Set.range ⇑g.base ⊆ Set.range ⇑(g.opensRange ⊔ V : X.Opens).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact le_sup_left
  obtain ⟨g₀, _, hg₀⟩ := exists_isOpenImmersion_factor g _ hgsub
  obtain ⟨R₁, β₁, hR₁p, hR₁T, i₁, p₁, hip₁, hiβ₁⟩ :=
    exists_isPerfect_lift_sup T hT E hE g hgc V hV hTV g₀ hg₀ P hP hPT
      (α ≫ (restrictCompIso g₀ (g.opensRange ⊔ V : X.Opens).ι g hg₀).inv.app E)
  obtain ⟨R, β, hRp, hRT, i₂, p₂, hip₂, hiβ₂⟩ := IH R₁ hR₁p hR₁T β₁
  exact ⟨R, β, hRp, hRT, _, _,
    retract_comp_of_iso (restrictCompIso g₀ (g.opensRange ⊔ V : X.Opens).ι g hg₀)
      hip₁ hiβ₁ hip₂ hiβ₂⟩

/-- **The induction of [Stacks, Tag 09IM] over a list of affine opens.** If the image of the open
immersion `g` together with the affine opens in `s` covers `X`, every map out of a perfect object
on the source of `g` supported on the preimage of `T` comes from a map out of a perfect object on
`X` supported on `T`, with the given object a direct summand of its restriction.

The induction is on the length of `s`, which is the induction on `m` of the source: the empty list
is the case where `g` is already surjective, handled by
`Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_range_eq_univ`, and the step is
`Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_step`. -/
theorem exists_isPerfect_lift_of_list {X : Scheme.{u}} [QuasiSeparatedSpace X] (T : Set X)
    (hT : IsClosed T)
    (hTc : ∀ W : X.Opens, IsCompact (W : Set X) → IsCompact ((W : Set X) ∩ Tᶜ))
    (E : DerivedCategory X.Modules)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := X.ringCatSheaf) E) :
    ∀ (s : List X.affineOpens) {Y : Scheme.{u}} (g : Y ⟶ X) (_ : IsOpenImmersion g),
      IsCompact (Set.range ⇑g.base) →
      (∀ x : X, x ∈ Set.range ⇑g.base ∨ ∃ V ∈ s, x ∈ ((V : X.Opens) : Set X)) →
      ∀ (P : DerivedCategory Y.Modules), IsPerfect (X := ringedSpace Y) P →
        CohomologySupportedOn Y.ringCatSheaf (⇑g.base ⁻¹' T) P →
        ∀ α : P ⟶ (derivedRestrict g).obj E,
        ∃ (R : DerivedCategory X.Modules) (β : R ⟶ E),
          IsPerfect (X := ringedSpace X) R ∧
          CohomologySupportedOn X.ringCatSheaf T R ∧
          ∃ (i : P ⟶ (derivedRestrict g).obj R) (p : (derivedRestrict g).obj R ⟶ P),
            i ≫ p = 𝟙 P ∧ i ≫ (derivedRestrict g).map β = α := by
  intro s
  induction s with
  | nil =>
      intro Y g hg hgc hcover P hP hPT α
      have := hg
      refine exists_isPerfect_lift_of_range_eq_univ g (fun x => ?_) T hT E hE P hP hPT α
      rcases hcover x with h | ⟨V, hVmem, -⟩
      · exact h
      · simp at hVmem
  | cons V s' ih =>
      intro Y g hg hgc hcover P hP hPT α
      have := hg
      refine exists_isPerfect_lift_step T hT E hE g hgc (V : X.Opens) V.2
        (hTc (V : X.Opens) V.2.isCompact) P hP hPT α ?_
      intro R₁ hR₁p hR₁T β₁
      have hsup : ((g.opensRange ⊔ (V : X.Opens) : X.Opens) : Set X) =
          Set.range ⇑g.base ∪ ((V : X.Opens) : Set X) := rfl
      refine ih (g.opensRange ⊔ (V : X.Opens) : X.Opens).ι inferInstance ?_ ?_ R₁ hR₁p hR₁T β₁
      · rw [Scheme.Opens.range_ι, hsup]
        exact hgc.union V.2.isCompact
      · intro x
        rw [Scheme.Opens.range_ι, hsup]
        rcases hcover x with h | ⟨W, hWmem, hxW⟩
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 hWmem with rfl | hW'
          · exact Or.inl (Or.inr hxW)
          · exact Or.inr ⟨W, hW', hxW⟩

/-- **[Stacks, Tag 09IM].** Let `X` be a quasi-compact quasi-separated scheme, `U ⊆ X` a
quasi-compact open, `T ⊆ X` a closed subset whose complement is retrocompact in `X`, and `E` an
object of `D_QCoh(𝒪_X)`. Every map `α : P ⟶ E|_U` out of a perfect object `P` of `D(𝒪_U)` whose
cohomology is supported on `T ∩ U` comes from a map `β : R ⟶ E` out of a perfect object `R` of
`D(𝒪_X)` whose cohomology is supported on `T`, with `P` a direct summand of `R|_U` by an inclusion
`i` satisfying `i ≫ β|_U = α`.

Quasi-compactness of `X` gives a finite cover of `X` by affine opens; the statement then follows
from `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_list` by the induction over that
cover, whose single step glues the object already built over a smaller open to the one the affine
case produces over the next affine. -/
@[stacks 09IM]
theorem exists_isPerfect_lift {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) (T : Set X) (hT : IsClosed T)
    (hTc : ∀ W : X.Opens, IsCompact (W : Set X) → IsCompact ((W : Set X) ∩ Tᶜ))
    (E : DerivedCategory X.Modules)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := X.ringCatSheaf) E)
    (P : DerivedCategory U.toScheme.Modules) (hP : IsPerfect (X := ringedSpace U.toScheme) P)
    (hPT : CohomologySupportedOn U.toScheme.ringCatSheaf (⇑U.ι.base ⁻¹' T) P)
    (α : P ⟶ (derivedRestrict U.ι).obj E) :
    ∃ (R : DerivedCategory X.Modules) (β : R ⟶ E),
      IsPerfect (X := ringedSpace X) R ∧
      CohomologySupportedOn X.ringCatSheaf T R ∧
      ∃ (i : P ⟶ (derivedRestrict U.ι).obj R) (p : (derivedRestrict U.ι).obj R ⟶ P),
        i ≫ p = 𝟙 P ∧ i ≫ (derivedRestrict U.ι).map β = α := by
  classical
  have htop : IsCompact ((⊤ : X.Opens) : Set X) := by
    simpa using isCompact_univ (X := X)
  obtain ⟨s, hsfin, hs⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp htop
  refine exists_isPerfect_lift_of_list T hT hTc E hE hsfin.toFinset.toList U.ι inferInstance
    (by rwa [Scheme.Opens.range_ι]) (fun x => Or.inr ?_) P hP hPT α
  have hx : x ∈ (⨆ i ∈ s, (i : X.Opens)) := by rw [← hs]; trivial
  simp only [Opens.mem_iSup] at hx
  obtain ⟨V, hVs, hxV⟩ := hx
  exact ⟨V, by simpa using hVs, hxV⟩

end Stacks.Perfect.LiftingComplexes

end
