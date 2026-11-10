module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasJointSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LiftAlongAffineStages
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerLimitTower
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOpenRepresentability

/-!
# Algebraic spaces along étale limit towers

Let `F` be an algebraic space over `S` and `Wₙ ⟶ V` an étale limit tower
(`AlgebraicGeometry.C1590Private.IsEtaleLimitTower`). Then `F(V) = lim F(Wₙ)`: every compatible
sequence of points of `F` over the `Wₙ` comes from exactly one point over `V`.

The proof lifts points étale locally to an atlas `U ⟶ F`. A lift over the closed level `W₀`
extends uniquely along the thickenings `W₀ ⟶ Wₙ`, the atlas being étale (Stacks 039R); the
lifts land in an affine open of `U`, so they glue over `V` by the limit property of the tower;
and the local points descend because `F` is a sheaf, the overlaps being handled by the same
argument applied to two points.

## Main results

* `AlgebraicGeometry.C1590Private.IsEtaleLimitTower.algebraicSpace_ext`: two points over `V`
  agreeing over every `Wₙ` are equal.
* `AlgebraicGeometry.C1590Private.IsEtaleLimitTower.algebraicSpace_existsUnique`: `F(V) =
  lim F(Wₙ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- A morphism of schemes between objects of the site, compatible with their structure morphisms,
as a morphism of the site. -/
def siteHomOfToScheme {X Y : BigFppfOver B S hS} (g : (𝒯).obj X ⟶ (𝒯).obj Y)
    (hg : g ≫ Y.hom.hom = X.hom.hom) : X ⟶ Y :=
  Over.homMk (ObjectProperty.homMk g) (ObjectProperty.hom_ext _ hg)

/-- The morphism of schemes underlying `siteHomOfToScheme g hg` is `g`. -/
@[simp]
theorem toScheme_map_siteHomOfToScheme {X Y : BigFppfOver B S hS} (g : (𝒯).obj X ⟶ (𝒯).obj Y)
    (hg : g ≫ Y.hom.hom = X.hom.hom) : (𝒯).map (siteHomOfToScheme g hg) = g := rfl

/-- A section of a morphism of the site, given as a morphism of schemes, is one of the site. -/
def sectionOfToScheme {X Y : BigFppfOver B S hS} (p : Y ⟶ X) (g : (𝒯).obj X ⟶ (𝒯).obj Y)
    (hg : g ≫ (𝒯).map p = 𝟙 _) : X ⟶ Y :=
  siteHomOfToScheme g (by
    have hw : (𝒯).map p ≫ X.hom.hom = Y.hom.hom := congrArg (fun k => k.hom) (Over.w p)
    rw [← hw, ← Category.assoc, hg, Category.id_comp])

/-- The étale property of an atlas, as a morphism property of presheaves. -/
abbrev IsEtaleAtlasMap {U : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : yoneda.obj U ⟶ F) : Prop :=
  (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f

/-- **Lifts to an étale atlas are unique along thickenings.** Two morphisms `T ⟶ U` to an étale
atlas `f : U ⟶ F` with the same composite to `F` which agree after a thickening `T₀ ⟶ T` are
equal. -/
theorem atlas_ext {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U T T₀ : BigFppfOver B S hS}
    {f : yoneda.obj U ⟶ F} (het : IsEtaleAtlasMap f) (d : T₀ ⟶ T)
    (hd : Stacks.Thickenings.IsThickening ((𝒯).map d)) {g g' : T ⟶ U}
    (hgg : yoneda.map g ≫ f = yoneda.map g' ≫ f) (hdg : d ≫ g = d ≫ g') : g = g' := by
  let z := yoneda.map g ≫ f
  let hrep := het.rep
  have : Etale ((𝒯).map (hrep.snd z)) := het.property_snd z
  let s : T ⟶ hrep.pullback z := hrep.lift' g (𝟙 T) (by simp [z])
  let s' : T ⟶ hrep.pullback z := hrep.lift' g' (𝟙 T) (by simp [z, hgg])
  have hss : s = s' := by
    apply (𝒯).map_injective
    refine ext_of_etale_of_isThickening ((𝒯).map d) hd ((𝒯).map (hrep.snd z)) ?_ ?_
    · rw [← Functor.map_comp, ← Functor.map_comp]
      simp [s, s']
    · rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply hrep.hom_ext'
      · simp [s, s', hdg]
      · simp [s, s']
  have h1 : s ≫ hrep.fst' z = g := hrep.lift'_fst _ _ _
  have h2 : s' ≫ hrep.fst' z = g' := hrep.lift'_fst _ _ _
  rw [← h1, ← h2, hss]

/-- A morphism `T₀ ⟶ U` to an étale atlas `f : U ⟶ F`, compatible with a point `z` of `F` over `T`
along a thickening `d : T₀ ⟶ T`, extends to a morphism `T ⟶ U` over `z`. -/
private theorem exists_lift_of_isThickening {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U T T₀ : BigFppfOver B S hS} {f : yoneda.obj U ⟶ F} (het : IsEtaleAtlasMap f) (d : T₀ ⟶ T)
    (hd : Stacks.Thickenings.IsThickening ((𝒯).map d)) (z : yoneda.obj T ⟶ F) (α₀ : T₀ ⟶ U)
    (hα₀ : yoneda.map α₀ ≫ f = yoneda.map d ≫ z) :
    ∃ β : T ⟶ U, yoneda.map β ≫ f = z ∧ d ≫ β = α₀ := by
  let hrep := het.rep
  have : Etale ((𝒯).map (hrep.snd z)) := het.property_snd z
  let σ : T₀ ⟶ hrep.pullback z := hrep.lift' α₀ d hα₀
  obtain ⟨τ, ⟨hτ, hτσ⟩, -⟩ := existsUnique_section_of_isThickening ((𝒯).map d) hd
    ((𝒯).map (hrep.snd z)) ((𝒯).map σ) (by rw [← Functor.map_comp]; simp [σ])
  let τ' := sectionOfToScheme (hrep.snd z) τ hτ
  have hτ' : τ' ≫ hrep.snd z = 𝟙 _ := (𝒯).map_injective (by
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]; exact hτ)
  have hdτ : d ≫ τ' = σ := (𝒯).map_injective (by rw [Functor.map_comp]; exact hτσ)
  refine ⟨τ' ≫ hrep.fst' z, ?_, ?_⟩
  · rw [Functor.map_comp, Category.assoc, (hrep.isPullback' z).w, ← Category.assoc,
      ← Functor.map_comp, hτ', CategoryTheory.Functor.map_id, Category.id_comp]
  · rw [← Category.assoc, hdτ]
    simp [σ]

/-- **An affine refinement of a surjective morphism, adapted to a morphism to a scheme.** For
`p : P ⟶ V` surjective and `α : P ⟶ X`, there are affine open subobjects `P' i` of `P`, each
mapped by `α` into an affine open `O i` of `X`, whose images cover `V`. -/
theorem exists_affine_refinement {P V : BigFppfOver B S hS} (p : P ⟶ V)
    (hp : Function.Surjective ((𝒯).map p)) {X : Scheme.{u}} (α : (𝒯).obj P ⟶ X) :
    ∃ (I : Type (u + 1)) (O' : I → ((𝒯).obj P).Opens) (O : I → X.Opens),
      (∀ i, IsAffineOpen (O' i)) ∧ (∀ i, IsAffineOpen (O i)) ∧
      (∀ i, ((O' i : Set ((𝒯).obj P))) ⊆ α ⁻¹' (O i)) ∧
      ∀ v : (𝒯).obj V, ∃ i, v ∈ Set.range ((O' i).ι ≫ (𝒯).map p) := by
  choose y hy using hp
  have hO : ∀ v : (𝒯).obj V, ∃ W : X.Opens, IsAffineOpen W ∧ α (y v) ∈ W := fun v => by
    obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := α (y v)) trivial
    exact ⟨W, hW, hxW⟩
  choose O hOa hOm using hO
  have hO' : ∀ v, ∃ W : ((𝒯).obj P).Opens, IsAffineOpen W ∧ y v ∈ W ∧ W.1 ⊆ (α ⁻¹ᵁ O v).1 :=
    fun v => exists_isAffineOpen_mem_and_subset (show y v ∈ α ⁻¹ᵁ O v from hOm v)
  choose O' hO'a hO'm hO'sub using hO'
  refine ⟨ULift.{u + 1} ((𝒯).obj V), fun v => O' v.down, fun v => O v.down, fun v => hO'a _,
    fun v => hOa _, fun v => hO'sub _, fun v => ⟨⟨v⟩, ⟨y v, hO'm v⟩, ?_⟩⟩
  exact hy v

section Tower

variable {V : BigFppfOver B S hS} {W : ℕ → BigFppfOver B S hS} {κ : ∀ n, W n ⟶ V}
  {ℓ : ∀ n, W n ⟶ W (n + 1)} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Two points over the top of an étale limit tower agree once one of them lifts to the atlas
into an affine open and they agree on every level.** -/
theorem IsEtaleLimitTower.eq_of_lift (hW : IsEtaleLimitTower W κ ℓ) {U : BigFppfOver B S hS}
    {f : yoneda.obj U ⟶ F} (het : IsEtaleAtlasMap f) (x y : F.obj (op V)) (α : V ⟶ U)
    (hα : yoneda.map α ≫ f = yonedaEquiv.symm x) (O : ((𝒯).obj U).Opens) (hO : IsAffineOpen O)
    (hαO : Set.range ((𝒯).map α) ⊆ O) (h : ∀ n, F.map (κ n).op x = F.map (κ n).op y) :
    x = y := by
  let ya := yonedaEquiv.symm y
  have hκ : ∀ n, yoneda.map (κ n ≫ α) ≫ f = yoneda.map (κ n) ≫ ya := fun n => by
    rw [Functor.map_comp, Category.assoc, hα, yonedaEquiv_symm_naturality_left,
      yonedaEquiv_symm_naturality_left, h n]
  obtain ⟨β, hβ, hκβ⟩ := exists_lift_of_isThickening het (κ 0) hW.isThickening_zero ya (κ 0 ≫ α)
    (hκ 0)
  have hlev : ∀ n, κ n ≫ α = κ n ≫ β := fun n => by
    refine atlas_ext het (towerToLevel ℓ n) (hW.isThickening_towerToLevel n) ?_ ?_
    · rw [hκ n, Functor.map_comp, Category.assoc, hβ]
    · rw [← Category.assoc, ← Category.assoc, hW.towerToLevel_comp, hκβ]
  have hβO : Set.range ((𝒯).map β) ⊆ O := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨w, rfl⟩ := hW.isThickening_zero.2 v
    have e := congrArg (fun k => (𝒯).map k w) (hlev 0)
    simp only [Functor.map_comp, Scheme.Hom.comp_apply] at e
    rw [← e]
    exact hαO ⟨_, rfl⟩
  have hαβ : α = β := (𝒯).map_injective (hW.ext_of_range_subset O hO hαO hβO (fun n => by
    rw [← Functor.map_comp, ← Functor.map_comp, hlev n]))
  have : yonedaEquiv.symm x = yonedaEquiv.symm y := by rw [← hα, hαβ, hβ]
  exact yonedaEquiv.symm.injective this

/-- The transition maps of the chosen base change of a tower. -/
abbrev towerPullbackMap (hW : IsEtaleLimitTower W κ ℓ) {P : BigFppfOver B S hS} (e : P ⟶ V)
    (n : ℕ) : pullback e (κ n) ⟶ pullback e (κ (n + 1)) :=
  pullback.map e (κ n) e (κ (n + 1)) (𝟙 _) (ℓ n) (𝟙 _) (by simp) (by simp [hW.comp n])

/-- The chosen base change of an étale limit tower to an affine object étale over its top is an
étale limit tower. -/
theorem IsEtaleLimitTower.pullbackTower (hW : IsEtaleLimitTower W κ ℓ) {P : BigFppfOver B S hS}
    (e : P ⟶ V) (he : Etale ((𝒯).map e)) (hP : IsAffine ((𝒯).obj P)) :
    IsEtaleLimitTower (fun n => pullback e (κ n)) (fun n => pullback.fst e (κ n))
      (towerPullbackMap hW e) :=
  hW.of_isPullback e he hP _ _ (fun n => pullback.snd e (κ n)) _
    (fun n => (IsPullback.of_hasPullback _ _).map 𝒯) (fun n => by simp) (fun n => by simp)

/-- **Points of an algebraic space over the top of an étale limit tower are determined by their
restrictions to the levels.** -/
theorem IsEtaleLimitTower.algebraicSpace_ext (hW : IsEtaleLimitTower W κ ℓ)
    (hF : IsAlgebraicSpace B S hS F) (x y : F.obj (op V))
    (h : ∀ n, F.map (κ n).op x = F.map (κ n).op y) : x = y := by
  obtain ⟨U, f, hsurj, het⟩ := hF.exists_atlas
  let xa := yonedaEquiv.symm x
  let hrep := het.rep
  let pa := hrep.snd xa
  have hsurj' : Surjective ((𝒯).map pa) := hsurj.property xa _ _ (hrep.isPullback' xa)
  obtain ⟨I, O', O, hO'a, hOa, hsub, hcov⟩ :=
    exists_affine_refinement pa hsurj'.surj ((𝒯).map (hrep.fst' xa))
  let P' : I → BigFppfOver B S hS := fun i => BigFppfOver.opensRestrictObj B S hS _ (O' i)
  let ι' : ∀ i, P' i ⟶ hrep.pullback xa := fun i =>
    BigFppfOver.opensRestrictHom B S hS _ (O' i)
  let r : ∀ i, P' i ⟶ V := fun i => ι' i ≫ pa
  have hr_et : ∀ i, Etale ((𝒯).map (r i)) := fun i => by
    have : Etale ((𝒯).map pa) := het.property_snd xa
    have : IsOpenImmersion ((𝒯).map (ι' i)) := inferInstanceAs (IsOpenImmersion (O' i).ι)
    rw [Functor.map_comp]
    infer_instance
  have hcovS : Sieve.ofArrows P' r ∈ BigFppfOver.topology B S hS V :=
    BigFppfOver.ofArrows_mem_topology_of_etale B S hS P' r hr_et hcov
  have hsep : Presieve.IsSeparatedFor F (Presieve.ofArrows P' r) :=
    Presieve.isSeparatedFor_iff_generate.2
      ((((isSheaf_iff_isSheaf_of_type _ _).1 hF.isSheaf) _ hcovS).isSeparatedFor)
  refine hsep.ext fun Z g hg => ?_
  rcases hg with ⟨i⟩
  have hWi := hW.pullbackTower (r i) (hr_et i) (hO'a i)
  refine hWi.eq_of_lift het (F.map (r i).op x) (F.map (r i).op y) (ι' i ≫ hrep.fst' xa) ?_
    (O i) (hOa i) ?_ (fun n => ?_)
  · rw [← yonedaEquiv_symm_naturality_left, Functor.map_comp, Category.assoc,
      (hrep.isPullback' xa).w, ← Category.assoc, ← Functor.map_comp]
  · rintro _ ⟨v, rfl⟩
    exact hsub i v.2
  · simp only [← Functor.map_comp_apply, ← op_comp]
    rw [pullback.condition]
    simp only [op_comp, Functor.map_comp_apply, h n]

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- Points of the underlying scheme of a fibre product of the site. -/
theorem exists_preimage_toScheme_pullback {X Y Z : BigFppfOver B S hS} (a : X ⟶ Z) (b : Y ⟶ Z)
    (x : (𝒯).obj X) (y : (𝒯).obj Y) (h : (𝒯).map a x = (𝒯).map b y) :
    ∃ z, (𝒯).map (pullback.fst a b) z = x ∧ (𝒯).map (pullback.snd a b) z = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  refine ⟨(PreservesPullback.iso 𝒯 a b).inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_fst, hz₁]
  · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_snd, hz₂]

/-- A compatible sequence of points over the levels of a tower restricts to its first term. -/
theorem map_towerToLevel {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : ℕ → BigFppfOver B S hS}
    (ℓ : ∀ n, W n ⟶ W (n + 1)) (s : ∀ n, F.obj (op (W n)))
    (hs : ∀ n, F.map (ℓ n).op (s (n + 1)) = s n) (n : ℕ) :
    F.map (towerToLevel ℓ n).op (s n) = s 0 := by
  induction n with
  | zero => simp [towerToLevel]
  | succ n ih => rw [towerToLevel, op_comp, Functor.map_comp_apply, hs, ih]

/-- The second projections `pullback e (κ n) ⟶ W n` intertwine the composite transition maps
`towerToLevel` of the base change of a tower along `e : P ⟶ V` with those of the tower. -/
theorem towerToLevel_pullbackMap_snd (hW : IsEtaleLimitTower W κ ℓ) {P : BigFppfOver B S hS}
    (e : P ⟶ V) (n : ℕ) :
    towerToLevel (towerPullbackMap hW e) n ≫ pullback.snd e (κ n) =
      pullback.snd e (κ 0) ≫ towerToLevel ℓ n := by
  induction n with
  | zero => simp [towerToLevel]
  | succ n ih =>
    simp only [towerToLevel, Category.assoc, towerPullbackMap, pullback.lift_snd]
    rw [← Category.assoc, ih, Category.assoc]

/-- **A compatible sequence of points over the levels of an étale limit tower whose first term
lifts to the atlas into an affine open comes from a point over the top**, the base `S` being
affine. -/
theorem IsEtaleLimitTower.exists_of_lift [IsAffine S] (hW : IsEtaleLimitTower W κ ℓ)
    {U : BigFppfOver B S hS} {f : yoneda.obj U ⟶ F} (het : IsEtaleAtlasMap f)
    (s : ∀ n, F.obj (op (W n))) (hs : ∀ n, F.map (ℓ n).op (s (n + 1)) = s n) (α₀ : W 0 ⟶ U)
    (hα₀ : yoneda.map α₀ ≫ f = yonedaEquiv.symm (s 0)) (O : ((𝒯).obj U).Opens)
    (hO : IsAffineOpen O) (hα₀O : Set.range ((𝒯).map α₀) ⊆ O) :
    ∃ t : F.obj (op V), ∀ n, F.map (κ n).op t = s n := by
  let z := fun n => yonedaEquiv.symm (s n)
  have hz : ∀ n, yoneda.map α₀ ≫ f = yoneda.map (towerToLevel ℓ n) ≫ z n := fun n => by
    rw [hα₀, yonedaEquiv_symm_naturality_left, map_towerToLevel ℓ s hs n]
  have key : ∀ n, ∃ αn : W n ⟶ U, yoneda.map αn ≫ f = z n ∧ towerToLevel ℓ n ≫ αn = α₀ :=
    fun n => exists_lift_of_isThickening het (towerToLevel ℓ n) (hW.isThickening_towerToLevel n)
      (z n) α₀ (hz n)
  choose α hα hαα using key
  have hcomp : ∀ n, ℓ n ≫ α (n + 1) = α n := fun n => by
    refine atlas_ext het (towerToLevel ℓ n) (hW.isThickening_towerToLevel n) ?_ ?_
    · rw [Functor.map_comp, Category.assoc, hα, hα, yonedaEquiv_symm_naturality_left, hs]
    · rw [← Category.assoc, ← towerToLevel, hαα, hαα]
  have hrange : ∀ n, Set.range ((𝒯).map (α n)) ⊆ O := fun n => by
    rintro _ ⟨v, rfl⟩
    obtain ⟨w, rfl⟩ := (hW.isThickening_towerToLevel n).2 v
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hαα]
    exact hα₀O ⟨_, rfl⟩
  obtain ⟨g, -, hg⟩ := hW.exists_hom_of_range_subset O hO (fun n => (𝒯).map (α n))
    (fun n => by rw [← Functor.map_comp, hcomp]) hrange
  have hgS : g ≫ U.hom.hom = V.hom.hom := by
    refine hW.ext_of_range_subset ⊤ (isAffineOpen_top S) (fun _ _ => trivial) (fun _ _ => trivial)
      (fun n => ?_)
    rw [← Category.assoc, hg]
    exact (congrArg (fun k => k.hom) (Over.w (α n))).trans
      (congrArg (fun k => k.hom) (Over.w (κ n))).symm
  let αV : V ⟶ U := siteHomOfToScheme g hgS
  refine ⟨yonedaEquiv (yoneda.map αV ≫ f), fun n => ?_⟩
  have hκα : κ n ≫ αV = α n := (𝒯).map_injective (by rw [Functor.map_comp]; exact hg n)
  rw [yonedaEquiv_naturality, ← Category.assoc, ← Functor.map_comp, hκα, hα]
  exact yonedaEquiv.apply_symm_apply _

/-- The first projection of a pullback in the site is étale on schemes when the second morphism
is. -/
theorem etale_toScheme_pullback_fst {X Y Z : BigFppfOver B S hS} (a : X ⟶ Z) (b : Y ⟶ Z)
    [Etale ((𝒯).map b)] : Etale ((𝒯).map (pullback.fst a b)) := by
  rw [← PreservesPullback.iso_hom_fst 𝒯 a b]
  infer_instance

/-- The second projection of a pullback in the site is étale on schemes when the first morphism
is. -/
theorem etale_toScheme_pullback_snd {X Y Z : BigFppfOver B S hS} (a : X ⟶ Z) (b : Y ⟶ Z)
    [Etale ((𝒯).map a)] : Etale ((𝒯).map (pullback.snd a b)) := by
  rw [← PreservesPullback.iso_hom_snd 𝒯 a b]
  infer_instance

/-- **`F(V) = lim F(Wₙ)` for an algebraic space `F` over an affine scheme and an étale limit
tower `Wₙ ⟶ V`.** Every compatible sequence of points of `F` over the levels comes from exactly
one point over the top. -/
theorem IsEtaleLimitTower.algebraicSpace_existsUnique [IsAffine S] (hW : IsEtaleLimitTower W κ ℓ)
    (hF : IsAlgebraicSpace B S hS F) (s : ∀ n, F.obj (op (W n)))
    (hs : ∀ n, F.map (ℓ n).op (s (n + 1)) = s n) :
    ∃! t : F.obj (op V), ∀ n, F.map (κ n).op t = s n := by
  refine existsUnique_of_exists_of_unique ?_ (fun t t' ht ht' =>
    hW.algebraicSpace_ext hF t t' (fun n => (ht n).trans (ht' n).symm))
  obtain ⟨U, f, hsurj, het⟩ := hF.exists_atlas
  let hrep := het.rep
  let s₀ := yonedaEquiv.symm (s 0)
  let p₀ := hrep.snd s₀
  have : Etale ((𝒯).map p₀) := het.property_snd s₀
  have hsurj' : Surjective ((𝒯).map p₀) := hsurj.property s₀ _ _ (hrep.isPullback' s₀)
  obtain ⟨I, O', O, hO'a, hOa, hsub, hcov⟩ :=
    exists_affine_refinement p₀ hsurj'.surj ((𝒯).map (hrep.fst' s₀))
  let A : I → BigFppfOver B S hS := fun i => BigFppfOver.opensRestrictObj B S hS _ (O' i)
  let ι' : ∀ i, A i ⟶ hrep.pullback s₀ := fun i => BigFppfOver.opensRestrictHom B S hS _ (O' i)
  have hA_et : ∀ i, Etale ((𝒯).map (ι' i ≫ p₀)) := fun i => by
    have : IsOpenImmersion ((𝒯).map (ι' i)) := inferInstanceAs (IsOpenImmersion (O' i).ι)
    rw [Functor.map_comp]
    infer_instance
  have hlift : ∀ i, ∃ (Vi : BigFppfOver B S hS) (q : Vi ⟶ V) (b : A i ⟶ Vi),
      IsAffine ((𝒯).obj Vi) ∧ Etale ((𝒯).map q) ∧ IsPullback b (ι' i ≫ p₀) q (κ 0) :=
    fun i => FormalSpace.exists_isPullback_affine_etale_lift_of_isThickening (κ 0)
      hW.isThickening_zero (A i) (hO'a i) (ι' i ≫ p₀) (hA_et i)
  choose Vi q b hVa hqet hpb using hlift
  have hloc : ∀ i, ∃ t : F.obj (op (Vi i)), ∀ n,
      F.map (pullback.fst (q i) (κ n)).op t = F.map (pullback.snd (q i) (κ n)).op (s n) := by
    intro i
    have hWi := hW.pullbackTower (q i) (hqet i) (hVa i)
    let e₀ := (hpb i).isoPullback
    refine hWi.exists_of_lift het (fun n => F.map (pullback.snd (q i) (κ n)).op (s n)) ?_
      (e₀.inv ≫ ι' i ≫ hrep.fst' s₀) ?_ (O i) (hOa i) ?_
    · intro n
      simp only [← Functor.map_comp_apply, ← op_comp, towerPullbackMap,
        pullback.lift_snd]
      rw [op_comp, Functor.map_comp_apply, hs]
    · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        (hrep.isPullback' s₀).w, ← yonedaEquiv_symm_naturality_left, ← Functor.map_comp_assoc,
        ← Functor.map_comp_assoc]
      congr 2
      exact (hpb i).isoPullback_inv_snd
    · rintro _ ⟨v, rfl⟩
      simp only [Functor.map_comp, Scheme.Hom.comp_apply]
      exact hsub i ((𝒯).map (e₀.inv) v).2
  choose t ht using hloc
  have hrestr : ∀ i n {Z : BigFppfOver B S hS} (g : Z ⟶ Vi i) (ψ : Z ⟶ W n),
      g ≫ q i = ψ ≫ κ n → F.map g.op (t i) = F.map ψ.op (s n) := by
    intro i n Z g ψ hgψ
    have h1 : g = pullback.lift g ψ hgψ ≫ pullback.fst (q i) (κ n) := (pullback.lift_fst _ _ _).symm
    have h2 : ψ = pullback.lift g ψ hgψ ≫ pullback.snd (q i) (κ n) :=
      (pullback.lift_snd _ _ _).symm
    conv_lhs => rw [h1]
    conv_rhs => rw [h2]
    rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ht i n]
  have hcov' : ∀ v : (𝒯).obj V, ∃ i, v ∈ Set.range ((𝒯).map (q i)) := by
    intro v
    obtain ⟨w, rfl⟩ := hW.isThickening_zero.2 v
    obtain ⟨i, a, ha⟩ := hcov w
    refine ⟨i, (𝒯).map (b i) a, ?_⟩
    change ((𝒯).map (b i) ≫ (𝒯).map (q i)) a = _
    rw [← Functor.map_comp, (hpb i).w, Functor.map_comp]
    exact congrArg (fun x => (𝒯).map (κ 0) x) ha
  have hsheaf := ((isSheaf_iff_isSheaf_of_type _ _).1 hF.isSheaf) _
    (BigFppfOver.ofArrows_mem_topology_of_etale B S hS Vi q hqet hcov')
  rw [← Presieve.isSheafFor_iff_generate] at hsheaf
  obtain ⟨tt, htt, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsheaf t (by
    intro i j Z gi gj hij
    have hm1 : gi = pullback.lift gi gj hij ≫ pullback.fst (q i) (q j) :=
      (pullback.lift_fst _ _ _).symm
    have hm2 : gj = pullback.lift gi gj hij ≫ pullback.snd (q i) (q j) :=
      (pullback.lift_snd _ _ _).symm
    conv_lhs => rw [hm1]
    conv_rhs => rw [hm2]
    rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    congr 1
    have := hVa i
    have := hVa j
    have := hW.isAffine
    have := hqet i
    have := hqet j
    have := etale_toScheme_pullback_fst (q i) (q j)
    have het' : Etale ((𝒯).map (pullback.fst (q i) (q j) ≫ q i)) := by
      rw [Functor.map_comp]; infer_instance
    have hWij := hW.pullbackTower (pullback.fst (q i) (q j) ≫ q i) het'
      (IsAffine.of_isIso (PreservesPullback.iso 𝒯 (q i) (q j)).hom)
    refine hWij.algebraicSpace_ext hF _ _ (fun n => ?_)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      hrestr i n _ (pullback.snd _ (κ n)) (by rw [Category.assoc]; exact pullback.condition),
      hrestr j n _ (pullback.snd _ (κ n)) (by
        rw [Category.assoc, ← pullback.condition (f := q i) (g := q j)]
        exact pullback.condition)])
  refine ⟨tt, fun n => ?_⟩
  have hcovn : ∀ w : (𝒯).obj (W n), ∃ i, w ∈ Set.range ((𝒯).map (pullback.snd (q i) (κ n))) := by
    intro w
    obtain ⟨i, v, hv⟩ := hcov' ((𝒯).map (κ n) w)
    obtain ⟨z, -, hz⟩ := exists_preimage_toScheme_pullback (q i) (κ n) v w hv
    exact ⟨i, z, hz⟩
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1 hF.isSheaf) _
    (BigFppfOver.ofArrows_mem_topology_of_etale B S hS _ _
      (fun i => by have := hqet i; exact etale_toScheme_pullback_snd (q i) (κ n)) hcovn)
  rw [← Presieve.isSheafFor_iff_generate] at hsep
  refine hsep.isSeparatedFor.ext fun Z g hg => ?_
  rcases hg with ⟨i⟩
  rw [← Functor.map_comp_apply, ← op_comp, ← pullback.condition, op_comp,
    Functor.map_comp_apply, htt i, ht i n]

end Tower

end AlgebraicGeometry.C1590Private

end
