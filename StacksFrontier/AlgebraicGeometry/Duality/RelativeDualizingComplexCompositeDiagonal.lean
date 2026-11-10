module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex

/-!
# The diagonal open of a composite

Let `g : X ⟶ S` and `f : Y ⟶ X` be morphisms of schemes, let `W ⊆ X ×_S X` be an open through
which `Δ_{X/S}` factors as a closed immersion `Δ : X ⟶ W`, and let `V ⊆ Y ×_X Y` be an open
through which `Δ_{Y/X}` factors as a closed immersion `Δ' : Y ⟶ V`. The square

```
Y ×_X Y ──j──> Y ×_S Y
   │              │ f × f
   X ───Δ_{X/S}─> X ×_S X
```

is cartesian. Since `j` is an immersion, `V` is the preimage of an open of `Y ×_S Y`; intersecting
it with `(f × f)⁻¹(W)` gives an open `W' ⊆ Y ×_S Y` with `j⁻¹(W') = V` and `(f × f)(W') ⊆ W`.
Then

```
   V ───δ───> W'
   │m          │ f × f
   X ───Δ───> W
```

is cartesian, so `δ` is a closed immersion, and `Δ_{Y/S}` factors through the closed immersion
`δ ∘ Δ' : Y ⟶ W'`. This is the choice of opens in the proof of Stacks 0E30.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.comp`: the diagonal open `W'` of `f ≫ g`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.compδ`: the closed immersion `δ : V ⟶ W'`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.compProd`: the map `f × f : W' ⟶ W`, which is flat
  when `f` is.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isPullback_compδ`: the square above is cartesian.

## References

* [Stacks Project, Lemma 48.28.11 (Tag 0E30)](https://stacks.math.columbia.edu/tag/0E30)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X Y S : Scheme.{u}} {g : X ⟶ S} {f : Y ⟶ X}

/-- A square stays cartesian when its two maps into the corner are both followed by the same
monomorphism, read backwards. -/
theorem isPullback_of_postcomp_mono {C : Type*} [Category C]
    {P A B Z Z' : C} {fst : P ⟶ A} {snd : P ⟶ B} {a : A ⟶ Z} {b : B ⟶ Z} (ι : Z ⟶ Z') [Mono ι]
    (h : IsPullback fst snd (a ≫ ι) (b ≫ ι)) : IsPullback fst snd a b :=
  IsPullback.of_isLimit' ⟨by rw [← cancel_mono ι]; simpa using h.w⟩
    (PullbackCone.IsLimit.mk _
      (fun s => h.lift s.fst s.snd (by rw [reassoc_of% s.condition]))
      (fun s => by simp) (fun s => by simp)
      (fun s m h₁ h₂ => h.hom_ext (by simp [h₁]) (by simp [h₂])))

variable (g f)

/-- The immersion `j : Y ×_X Y ⟶ Y ×_S Y`. -/
abbrev compMap : pullback f f ⟶ pullback (f ≫ g) (f ≫ g) :=
  pullback.map f f (f ≫ g) (f ≫ g) (𝟙 _) (𝟙 _) g (by simp) (by simp)

/-- The map `f × f : Y ×_S Y ⟶ X ×_S X`. -/
abbrev prodMap : pullback (f ≫ g) (f ≫ g) ⟶ pullback g g :=
  pullback.map (f ≫ g) (f ≫ g) g g f f (𝟙 _) (by simp) (by simp)

/-- `Y ×_X Y` is the preimage of the diagonal of `X ×_S X` under `f × f`. -/
theorem isPullback_compMap :
    IsPullback (pullback.fst f f ≫ f) (compMap g f) (pullback.diagonal g) (prodMap g f) :=
  pullback_map_diagonal_isPullback f f g

/-- The map `j : Y ×_X Y ⟶ Y ×_S Y` is an immersion. -/
instance : IsImmersion (compMap g f) :=
  MorphismProperty.of_isPullback (P := @IsImmersion) (isPullback_compMap g f)
    (inferInstance : IsImmersion (pullback.diagonal g))

/-- `Δ_{Y/S} = j ∘ Δ_{Y/X}`. -/
theorem diagonal_comp_compMap :
    pullback.diagonal f ≫ compMap g f = pullback.diagonal (f ≫ g) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, pullback.diagonal_fst,
      pullback.diagonal_fst]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, pullback.diagonal_snd,
      pullback.diagonal_snd]

/-- If `f` is flat, then so is `f × f : Y ×_S Y ⟶ X ×_S X`. -/
theorem flat_prodMap [Flat f] : Flat (prodMap g f) :=
  MorphismProperty.pullbackMap (P := @Flat) (inferInstanceAs (Flat f))
    (inferInstanceAs (Flat f)) rfl rfl

variable {g f} (Dg : DiagonalOpen g) (Df : DiagonalOpen f)

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

/-- `(f × f)⁻¹(W)`. -/
abbrev compBase : (pullback (f ≫ g) (f ≫ g)).Opens := prodMap g f ⁻¹ᵁ Dg.ι.opensRange

/-- The preimage of `(f × f)⁻¹(W)` under `j : Y ×_X Y ⟶ Y ×_S Y` is all of `Y ×_X Y`. -/
theorem compMap_preimage_compBase : compMap g f ⁻¹ᵁ Dg.compBase = ⊤ := by
  ext x
  simp only [Opens.map_coe, Hom.coe_opensRange, Set.mem_preimage, Opens.coe_top, Set.mem_univ,
    iff_true]
  refine ⟨Dg.diag.base ((pullback.fst f f ≫ f).base x), ?_⟩
  rw [← Scheme.Hom.comp_apply, Dg.fac, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    (isPullback_compMap g f).w]

/-- There is an open of `Y ×_S Y` whose preimage under `j : Y ×_X Y ⟶ Y ×_S Y` is `V`. -/
theorem exists_open_preimage_eq :
    ∃ U : (pullback (f ≫ g) (f ≫ g)).Opens, compMap g f ⁻¹ᵁ U = Df.ι.opensRange := by
  obtain ⟨t, ht, hts⟩ := (Scheme.Hom.isEmbedding (compMap g f)).isInducing.isOpen_iff.1
    Df.ι.opensRange.2
  exact ⟨⟨t, ht⟩, Opens.ext hts⟩

/-- The open `W' ⊆ Y ×_S Y`: an open with preimage `V` in `Y ×_X Y`, intersected with
`(f × f)⁻¹(W)`. -/
def compOpen : (pullback (f ≫ g) (f ≫ g)).Opens :=
  (exists_open_preimage_eq Df (g := g)).choose ⊓ Dg.compBase

/-- The preimage of `W'` under `j : Y ×_X Y ⟶ Y ×_S Y` is `V`. -/
theorem compMap_preimage_compOpen : compMap g f ⁻¹ᵁ Dg.compOpen Df = Df.ι.opensRange := by
  rw [compOpen, Scheme.Hom.preimage_inf, compMap_preimage_compBase, inf_top_eq]
  exact (exists_open_preimage_eq Df (g := g)).choose_spec

/-- The open `W'` is contained in `(f × f)⁻¹(W)`. -/
theorem compOpen_le_compBase : Dg.compOpen Df ≤ Dg.compBase := inf_le_right

/-- The image of `V` under `j : Y ×_X Y ⟶ Y ×_S Y` is contained in `W'`. -/
theorem range_compMap_le : Set.range (Df.ι ≫ compMap g f).base ⊆
    Set.range (Dg.compOpen Df).ι.base := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  have : Df.ι.base x ∈ compMap g f ⁻¹ᵁ Dg.compOpen Df := by
    rw [compMap_preimage_compOpen]; exact ⟨x, rfl⟩
  simpa using this

/-- The closed immersion `δ : V ⟶ W'`. -/
def compδ : Df.W ⟶ (Dg.compOpen Df).toScheme :=
  IsOpenImmersion.lift (Dg.compOpen Df).ι (Df.ι ≫ compMap g f) (Dg.range_compMap_le Df)

/-- The map `δ : V ⟶ W'` followed by the inclusion of `W'` is the inclusion of `V` followed by
`j : Y ×_X Y ⟶ Y ×_S Y`. -/
@[reassoc (attr := simp)]
theorem compδ_ι : Dg.compδ Df ≫ (Dg.compOpen Df).ι = Df.ι ≫ compMap g f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The image of `W'` under `f × f : Y ×_S Y ⟶ X ×_S X` is contained in `W`. -/
theorem range_compProd_le : Set.range ((Dg.compOpen Df).ι ≫ prodMap g f).base ⊆
    Set.range Dg.ι.base := by
  rintro _ ⟨x, rfl⟩
  have hx : (Dg.compOpen Df).ι.base x ∈ Dg.compBase := Dg.compOpen_le_compBase Df x.2
  simpa using hx

/-- The map `f × f : W' ⟶ W`. -/
def compProd : (Dg.compOpen Df).toScheme ⟶ Dg.W :=
  IsOpenImmersion.lift Dg.ι ((Dg.compOpen Df).ι ≫ prodMap g f) (Dg.range_compProd_le Df)

/-- The map `f × f : W' ⟶ W` followed by the inclusion of `W` is the inclusion of `W'` followed by
`f × f : Y ×_S Y ⟶ X ×_S X`. -/
@[reassoc (attr := simp)]
theorem compProd_ι : Dg.compProd Df ≫ Dg.ι = (Dg.compOpen Df).ι ≫ prodMap g f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The map `m : V ⟶ X`. -/
abbrev compBaseMap : Df.W ⟶ X := Df.ι ≫ pullback.fst f f ≫ f

/-- **The square of opens is cartesian**: `V = W' ×_W X`. -/
theorem isPullback_compδ :
    IsPullback Df.compBaseMap (Dg.compδ Df) Dg.diag (Dg.compProd Df) := by
  have h₁ : IsPullback (Dg.compδ Df) Df.ι (Dg.compOpen Df).ι (compMap g f) :=
    IsOpenImmersion.isPullback _ _ _ _ (by simp) (by
      rw [Scheme.Opens.opensRange_ι]; exact Dg.compMap_preimage_compOpen Df)
  have h₂ := h₁.flip.paste_horiz (isPullback_compMap g f)
  refine isPullback_of_postcomp_mono Dg.ι ?_
  rw [Dg.fac, compProd_ι]
  exact h₂

/-- The map `δ : V ⟶ W'` is a closed immersion. -/
instance : IsClosedImmersion (Dg.compδ Df) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (Dg.isPullback_compδ Df)
    (inferInstance : IsClosedImmersion Dg.diag)

/-- If `f` is flat, then so is `f × f : W' ⟶ W`. -/
theorem flat_compProd [Flat f] : Flat (Dg.compProd Df) := by
  have : Flat (prodMap g f) := flat_prodMap g f
  have hc : Flat (Dg.compProd Df ≫ Dg.ι) := by
    rw [compProd_ι]; exact MorphismProperty.comp_mem @Flat _ _ inferInstance this
  exact (MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
    (P := @Flat.{u})).of_postcomp _ Dg.ι (show Mono Dg.ι from inferInstance) hc

/-- **The diagonal open of a composite**: `W' ⊆ Y ×_S Y`, through which `Δ_{Y/S}` factors as the
closed immersion `δ ∘ Δ' : Y ⟶ W'`. -/
def comp : DiagonalOpen (f ≫ g) where
  W := (Dg.compOpen Df).toScheme
  ι := (Dg.compOpen Df).ι
  isOpenImmersion := inferInstance
  diag := Df.diag ≫ Dg.compδ Df
  isClosedImmersion := inferInstance
  fac := by rw [Category.assoc, compδ_ι, ← Category.assoc, Df.fac, diagonal_comp_compMap]

/-- The closed immersion `Y ⟶ W'` of the diagonal open of `f ≫ g` is `δ ∘ Δ'`. -/
theorem comp_diag : (Dg.comp Df).diag = Df.diag ≫ Dg.compδ Df := rfl

/-- The first projection of `W'` restricts to that of `V` along `δ`. -/
theorem compδ_proj : Dg.compδ Df ≫ (Dg.comp Df).proj = Df.proj := by
  change Dg.compδ Df ≫ (Dg.compOpen Df).ι ≫ pullback.fst _ _ = Df.ι ≫ pullback.fst _ _
  rw [compδ_ι_assoc, pullback.lift_fst, Category.comp_id]

/-- `f ∘ pr₁ = pr₁ ∘ (f × f)` on `W'`. -/
theorem comp_proj_comp : (Dg.comp Df).proj ≫ f = Dg.compProd Df ≫ Dg.proj := by
  change ((Dg.compOpen Df).ι ≫ pullback.fst _ _) ≫ f = Dg.compProd Df ≫ Dg.ι ≫ pullback.fst _ _
  rw [compProd_ι_assoc, pullback.lift_fst, Category.assoc]

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
