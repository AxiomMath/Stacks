module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact

/-!
# Rigidified Picard classes glue along fpqc coverings of an arbitrary base

Let `f : X ⟶ S` be a morphism of schemes with a section `σ`, and suppose that
`𝒪_T ⟶ (X_T ⟶ T)_* 𝒪_{X_T}` is an isomorphism for every `S`-scheme `T`, where `X_T = X ×_S T`.
For an `S`-scheme `T` let `σ_T : T ⟶ X_T` be the induced section. This file proves that the
Picard classes of `X_T` killed by `σ_T^*` form a sheaf for every family of `S`-schemes
`Uᵢ ⟶ T` whose base change `X_{Uᵢ} ⟶ X_T` is an fpqc covering:

* a class killed by `σ_T^*` and by every restriction to `X_{Uᵢ}` is zero
  (`Stacks.RigidifiedPicard.eq_zero_of_section_eq_zero`);
* classes on the `X_{Uᵢ}` killed by the induced sections and agreeing after every further
  pullback come from a class on `X_T` (`Stacks.RigidifiedPicard.exists_glue`).

## Main results

* `Stacks.RigidifiedPicard.eq_zero_of_section_eq_zero`: separatedness.
* `Stacks.RigidifiedPicard.exists_glue`: gluing.

## Implementation notes

The argument is that of the proof of [Stacks, Tag 0B9N], run with all `S`-schemes as test
schemes, which is the generality of
`AlgebraicGeometry.exists_grp_iso_of_representable_openSubfunctor` (Tag 0B9Q). The descent steps
`Stacks.Picard.normalizedHom`, `Stacks.Picard.diagramDescentData`,
`Stacks.Picard.nonempty_iso_of_pullHom_hom_eq` and
`Stacks.Picard.isInvertible_of_pullback_fpqcCover` are applied to the base-change functor
`Stacks.RigidifiedPicard.bcFunctor` on `Over S`.

## References

* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Base change along `S`-schemes -/

/-- The base change `X_T = X ×_S T` of `f` along an `S`-scheme `T`. -/
abbrev bc (T : Over S) : Scheme.{u} := pullback f T.hom

/-- The projection `X_T ⟶ T`. -/
abbrev bcProj (T : Over S) : bc f T ⟶ T.left := pullback.snd f T.hom

/-- The morphism `X_T ⟶ X_U` induced by a morphism of `S`-schemes `T ⟶ U`. -/
def bcMap {T U : Over S} (g : T ⟶ U) : bc f T ⟶ bc f U :=
  pullback.map f T.hom f U.hom (𝟙 _) g.left (𝟙 _) (by simp) (by simp)

/-- The map `X_T ⟶ X_U` commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem bcMap_fst {T U : Over S} (g : T ⟶ U) :
    bcMap f g ≫ pullback.fst f U.hom = pullback.fst f T.hom := by
  simp only [bcMap, pullback.map, pullback.lift_fst, Category.comp_id]

/-- The map `X_T ⟶ X_U` lies over `T ⟶ U`. -/
@[reassoc (attr := simp)]
theorem bcMap_snd {T U : Over S} (g : T ⟶ U) :
    bcMap f g ≫ bcProj f U = bcProj f T ≫ g.left := by
  simp only [bcMap, pullback.map, pullback.lift_snd]

/-- The base change of the identity is the identity. -/
@[simp]
theorem bcMap_id (T : Over S) : bcMap f (𝟙 T) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- The base change of a composite is the composite of the base changes. -/
theorem bcMap_comp {T U V : Over S} (g : T ⟶ U) (h : U ⟶ V) :
    bcMap f (g ≫ h) = bcMap f g ≫ bcMap f h := by
  apply pullback.hom_ext <;> simp

/-- The base change of a composite named by an equation. -/
theorem bcMap_comp_eq {T U W : Over S} (g : U ⟶ T) (b : W ⟶ U) (k : W ⟶ T) (hk : b ≫ g = k) :
    bcMap f b ≫ bcMap f g = bcMap f k := by
  rw [← bcMap_comp, hk]

/-- The base change, as a functor from `S`-schemes to schemes. -/
@[simps]
def bcFunctor : Over S ⥤ Scheme.{u} where
  obj T := bc f T
  map g := bcMap f g
  map_id T := bcMap_id f T
  map_comp g h := bcMap_comp f g h

/-- The base change of a morphism `a : U ⟶ T` sits in a pullback square over `a`:
`X_U = X_T ×_T U`. -/
theorem bcMap_isPullback_proj {U T : Over S} (a : U ⟶ T) :
    IsPullback (bcMap f a) (bcProj f U) (bcProj f T) a.left := by
  refine IsPullback.of_right ?_ (bcMap_snd f a) (IsPullback.of_hasPullback _ _)
  rw [bcMap_fst, Over.w a]
  exact IsPullback.of_hasPullback _ _

/-- The base change of a pullback square of `S`-schemes is a pullback square. -/
theorem bcMap_isPullback {W U V T : Over S} (p : W ⟶ U) (q : W ⟶ V) (a : U ⟶ T) (b : V ⟶ T)
    (h : IsPullback p.left q.left a.left b.left) (hw : p ≫ a = q ≫ b) :
    IsPullback (bcMap f p) (bcMap f q) (bcMap f a) (bcMap f b) := by
  refine Stacks.Limits.isPullback_of_isPullback_vert (bcMap_isPullback_proj f p)
    (bcMap_isPullback_proj f q) (bcMap_isPullback_proj f a) (bcMap_isPullback_proj f b) h ?_
  rw [← bcMap_comp, ← bcMap_comp, hw]

/-- The base change of a family of `S`-schemes over `T` whose underlying family is in a
precoverage stable under base change is in that precoverage. -/
theorem bc_mem_of_mem (K : Precoverage Scheme.{u}) [K.IsStableUnderBaseChange] {T : Over S}
    {ι : Type*} {U : ι → Over S} (g : ∀ i, U i ⟶ T)
    (hg : Presieve.ofArrows (fun i => (U i).left) (fun i => (g i).left) ∈ K T.left) :
    Presieve.ofArrows (fun i => bc f (U i)) (fun i => bcMap f (g i)) ∈ K (bc f T) :=
  Precoverage.mem_coverings_of_isPullback (fun i => (g i).left) hg (bcProj f T)
    (fun i => bcMap f (g i)) (fun i => bcProj f (U i)) (fun i => bcMap_isPullback_proj f (g i))

/-! ### Chosen fibre products -/

/-- The chosen fibre product of two morphisms of `S`-schemes, carried by the fibre product of
the underlying schemes. -/
def overChosenPullback {U V T : Over S} (a : U ⟶ T) (b : V ⟶ T) : ChosenPullback a b := by
  let W := Over.mk (pullback.fst a.left b.left ≫ U.hom)
  let p : W ⟶ U := Over.homMk (pullback.fst a.left b.left)
  let q : W ⟶ V := Over.homMk (pullback.snd a.left b.left) (by
    change pullback.snd a.left b.left ≫ V.hom = pullback.fst a.left b.left ≫ U.hom
    rw [← Over.w a, ← Over.w b, ← Category.assoc, ← Category.assoc, pullback.condition])
  have h : p ≫ a = q ≫ b := Over.OverMorphism.ext pullback.condition
  exact ⟨W, p, q, h, isLimitOfReflects (Over.forget S)
    ((isLimitMapConePullbackConeEquiv (Over.forget S) h).symm
      (IsPullback.of_hasPullback a.left b.left).isLimit), p ≫ a, rfl⟩

/-- The underlying square of schemes of the chosen fibre product is a pullback square. -/
theorem overChosenPullback_isPullback {U V T : Over S} (a : U ⟶ T) (b : V ⟶ T) :
    IsPullback (overChosenPullback a b).p₁.left (overChosenPullback a b).p₂.left a.left
      b.left :=
  IsPullback.of_hasPullback a.left b.left

/-- The square of base changes attached to the chosen fibre product is a fibre-product
square. -/
theorem isPullback_bcChosen {U V T : Over S} (a : U ⟶ T) (b : V ⟶ T) :
    IsPullback (bcMap f (overChosenPullback a b).p₁) (bcMap f (overChosenPullback a b).p₂)
      (bcMap f a) (bcMap f b) :=
  bcMap_isPullback f _ _ a b (overChosenPullback_isPullback a b)
    (overChosenPullback a b).condition

/-- The chosen wide fibre product of three morphisms of `S`-schemes. -/
def overChosenPullback₃ {U V W T : Over S} (a : U ⟶ T) (b : V ⟶ T) (c : W ⟶ T) :
    ChosenPullback₃ (overChosenPullback a b) (overChosenPullback b c) (overChosenPullback a c) :=
  Stacks.Limits.chosenPullback₃OfChosenPullback _ _ _
    (overChosenPullback (overChosenPullback a b).p₂ (overChosenPullback b c).p₁)

/-- The base change of the square of projections of the chosen triple fibre product is a
pullback square. -/
theorem isPullback_bcChosen₃ {U V W T : Over S} (a : U ⟶ T) (b : V ⟶ T) (c : W ⟶ T) :
    IsPullback (bcMap f (overChosenPullback₃ a b c).p₁₂)
      (bcMap f (overChosenPullback₃ a b c).p₂₃)
      (bcMap f (overChosenPullback a b).p₂) (bcMap f (overChosenPullback b c).p₁) :=
  isPullback_bcChosen f (overChosenPullback a b).p₂ (overChosenPullback b c).p₁

/-- The base change of a family of `S`-schemes, as a zero-hypercover of `X_T`. -/
def bcHypercover {T : Over S} {ι : Type (u + 1)} {U : ι → Over S} (g : ∀ i, U i ⟶ T) :
    PreZeroHypercover.{u + 1} (bc f T) where
  I₀ := ι
  X i := bc f (U i)
  f i := bcMap f (g i)

/-! ### The induced sections -/

variable (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- The section `σ_T : T ⟶ X_T` induced by the section `σ`. -/
def bcSection (T : Over S) : T.left ⟶ bc f T :=
  pullback.lift (T.hom ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

/-- The induced section `σ_T` is a section of the projection `X_T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem bcSection_comp_snd (T : Over S) : bcSection f σ hσ T ≫ bcProj f T = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The composite of `σ_T` with the projection `X_T ⟶ X` is `T ⟶ S ⟶ X`. -/
@[reassoc (attr := simp)]
theorem bcSection_comp_fst (T : Over S) :
    bcSection f σ hσ T ≫ pullback.fst f T.hom = T.hom ≫ σ :=
  pullback.lift_fst _ _ _

/-- The induced sections are compatible with the transition maps of the base changes. -/
theorem bcSection_comp_bcMap {T U : Over S} (g : T ⟶ U) :
    bcSection f σ hσ T ≫ bcMap f g = g.left ≫ bcSection f σ hσ U := by
  apply pullback.hom_ext
  · simp [Over.w_assoc g]
  · simp

/-- The induced sections, as a natural transformation from the forgetful functor to the base
change functor. -/
@[simps]
def bcSectionNatTrans : Over.forget S ⟶ bcFunctor f where
  app T := bcSection f σ hσ T
  naturality _ _ g := (bcSection_comp_bcMap f σ hσ g).symm

/-- Pullback along `σ_T^*` is a left inverse of pullback along the projection. -/
theorem schemePullbackClass_bcSection_bcProj (T : Over S) (x : Stacks.Picard.ofScheme T.left) :
    Stacks.Picard.schemePullbackClass (bcSection f σ hσ T)
      (Stacks.Picard.schemePullbackClass (bcProj f T) x) = x := by
  rw [Stacks.Picard.schemePullbackClass_comp, bcSection_comp_snd,
    Stacks.Picard.schemePullbackClass_id]

/-- Pullback along the induced section commutes with restriction. -/
theorem schemePullbackClass_bcSection_natural {T U : Over S} (g : T ⟶ U)
    (x : Stacks.Picard.ofScheme (bc f U)) :
    Stacks.Picard.schemePullbackClass (bcSection f σ hσ T)
        (Stacks.Picard.schemePullbackClass (bcMap f g) x) =
      Stacks.Picard.schemePullbackClass g.left
        (Stacks.Picard.schemePullbackClass (bcSection f σ hσ U) x) := by
  rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
    bcSection_comp_bcMap]

/-- Pullback along the projection commutes with restriction. -/
theorem schemePullbackClass_bcProj_natural {T U : Over S} (g : T ⟶ U)
    (x : Stacks.Picard.ofScheme U.left) :
    Stacks.Picard.schemePullbackClass (bcMap f g)
        (Stacks.Picard.schemePullbackClass (bcProj f U) x) =
      Stacks.Picard.schemePullbackClass (bcProj f T)
        (Stacks.Picard.schemePullbackClass g.left x) := by
  rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
    bcMap_snd]

/-! ### Normalised trivialisations -/

/-- For `g : U ⟶ T`, the composite `U ⟶ T ⟶ X_T` equals `U ⟶ X_U ⟶ X_T`. -/
theorem comp_bcSection_eq {U T : Over S} (g : U ⟶ T) :
    g.left ≫ bcSection f σ hσ T = bcSection f σ hσ U ≫ bcMap f g :=
  (bcSection_comp_bcMap f σ hσ g).symm

private theorem comp_sectionComp {T U W : Over S} (g : U ⟶ T) (b : W ⟶ U) (k : W ⟶ T)
    (hk : b ≫ g = k) :
    b.left ≫ (bcSection f σ hσ U ≫ bcMap f g) = bcSection f σ hσ W ≫ bcMap f k := by
  subst hk
  rw [← Category.assoc, ← bcSection_comp_bcMap f σ hσ b, Category.assoc, ← bcMap_comp]

/-- The restriction along a morphism of `S`-schemes of a homomorphism between the pullbacks of
two modules on `X_T` along the induced section of `T`. -/
def sectionRestrict {T : Over S} {L' M' : (bc f T).Modules}
    (β : (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj M')
    {U : Over S} (g : U ⟶ T) :
    (modulePullbackPseudofunctor.map (bcSection f σ hσ U ≫ bcMap f g).op.toLoc).toFunctor.obj
        L' ⟶
      (modulePullbackPseudofunctor.map (bcSection f σ hσ U ≫ bcMap f g).op.toLoc).toFunctor.obj
        M' :=
  pullHom β g.left _ _ (comp_bcSection_eq f σ hσ g) (comp_bcSection_eq f σ hσ g)

private theorem pullHom_sectionRestrict' {T : Over S} {L' M' : (bc f T).Modules}
    (β : (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj M')
    {U W : Over S} (g : U ⟶ T) (b : W ⟶ U) (k : W ⟶ T) (hk : b ≫ g = k) :
    pullHom (sectionRestrict f σ hσ β g) b.left _ _ (comp_sectionComp f σ hσ g b k hk)
        (comp_sectionComp f σ hσ g b k hk) =
      sectionRestrict f σ hσ β k := by
  subst hk
  exact Stacks.Picard.pullHom_pullHom_of_eq β g.left _ _ _ _ b.left (b ≫ g).left rfl _ _ _ _ _ _

private theorem sectionRestrict_hom_comp_inv {T : Over S} {L' M' : (bc f T).Modules}
    (β : (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj L' ≅
      (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj M')
    {U : Over S} (g : U ⟶ T) :
    sectionRestrict f σ hσ β.hom g ≫ sectionRestrict f σ hσ β.inv g = 𝟙 _ :=
  Stacks.Picard.pullHom_hom_comp_pullHom_inv β g.left _ _ _ _

/-- Two homomorphisms whose restrictions along the induced section are the restrictions of an
isomorphism and of its inverse compose to the identity. -/
private theorem comp_eq_id_of_pullHom_section_eq
    (hOiso : ∀ U : Over S, IsIso (bcProj f U).toLRSHom.toHom.c)
    {T : Over S} {L' M' : (bc f T).Modules}
    (hL' : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf (bc f T).ringCatSheaf.2 L')
    (β : (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj L' ≅
      (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj M')
    {U : Over S} (g : U ⟶ T)
    (a : (modulePullbackPseudofunctor.map (bcMap f g).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map (bcMap f g).op.toLoc).toFunctor.obj M')
    (b : (modulePullbackPseudofunctor.map (bcMap f g).op.toLoc).toFunctor.obj M' ⟶
      (modulePullbackPseudofunctor.map (bcMap f g).op.toLoc).toFunctor.obj L')
    (ha : pullHom a (bcSection f σ hσ U) _ _ rfl rfl = sectionRestrict f σ hσ β.hom g)
    (hb : pullHom b (bcSection f σ hσ U) _ _ rfl rfl = sectionRestrict f σ hσ β.inv g) :
    a ≫ b = 𝟙 _ := by
  refine (Stacks.Picard.bijective_pullHom_section' (bcMap f g) (bcMap f g) (bcProj f U)
    (bcSection f σ hσ U) (bcSection_comp_snd f σ hσ U) (hOiso U) L' L' hL' hL' (Iso.refl _) _ _
    rfl rfl).injective ?_
  change pullHom (a ≫ b) _ _ _ rfl rfl = pullHom (𝟙 _) _ _ _ rfl rfl
  rw [Stacks.Picard.pullHom_comp' a b (bcSection f σ hσ U) _ _ _ rfl rfl rfl, ha, hb,
    sectionRestrict_hom_comp_inv]
  exact (Stacks.Picard.pullHom_id' (F := modulePullbackPseudofunctor) L' (bcMap f g)
    (bcSection f σ hσ U) _ rfl).symm

/-- **The normalised trivialisation on a member of a family.** -/
private theorem exists_pullHom_eq_sectionRestrict
    (hOiso : ∀ U : Over S, IsIso (bcProj f U).toLRSHom.toHom.c)
    {T : Over S} (L' M' : (bc f T).Modules)
    (hL' : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf (bc f T).ringCatSheaf.2 L')
    (hM' : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf (bc f T).ringCatSheaf.2 M')
    (β : (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj L' ≅
      (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj M')
    {U : Over S} (g : U ⟶ T)
    (e : (modulePullbackPseudofunctor.map (bcMap f g).op.toLoc).toFunctor.obj L' ≅
      (modulePullbackPseudofunctor.map (bcMap f g).op.toLoc).toFunctor.obj M') :
    ∃ ψ : (modulePullbackPseudofunctor.map (bcMap f g).op.toLoc).toFunctor.obj L' ≅
        (modulePullbackPseudofunctor.map (bcMap f g).op.toLoc).toFunctor.obj M',
      pullHom ψ.hom (bcSection f σ hσ U) _ _ rfl rfl = sectionRestrict f σ hσ β.hom g := by
  have hsec : bcSection f σ hσ U ≫ bcProj f U = 𝟙 _ := bcSection_comp_snd f σ hσ U
  obtain ⟨a, ha⟩ := (Stacks.Picard.bijective_pullHom_section' (bcMap f g) (bcMap f g)
    (bcProj f U) (bcSection f σ hσ U) hsec (hOiso U) L' M' hL' hM' e _ _ rfl
    rfl).surjective (sectionRestrict f σ hσ β.hom g)
  obtain ⟨b, hb⟩ := (Stacks.Picard.bijective_pullHom_section' (bcMap f g) (bcMap f g)
    (bcProj f U) (bcSection f σ hσ U) hsec (hOiso U) M' L' hM' hL' e.symm _ _ rfl
    rfl).surjective (sectionRestrict f σ hσ β.inv g)
  have ha' : pullHom a (bcSection f σ hσ U) (bcSection f σ hσ U ≫ bcMap f g)
      (bcSection f σ hσ U ≫ bcMap f g) rfl rfl = sectionRestrict f σ hσ β.hom g := ha
  have hb' : pullHom b (bcSection f σ hσ U) (bcSection f σ hσ U ≫ bcMap f g)
      (bcSection f σ hσ U ≫ bcMap f g) rfl rfl = sectionRestrict f σ hσ β.inv g := hb
  exact ⟨⟨a, b, comp_eq_id_of_pullHom_section_eq f σ hσ hOiso hL' β g a b ha' hb',
    comp_eq_id_of_pullHom_section_eq f σ hσ hOiso hM' β.symm g b a hb' ha'⟩, ha'⟩

private theorem pullHom_section_pullHom_bcMap {T : Over S} {L' M' : (bc f T).Modules}
    (β : (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj M')
    {U W : Over S} (g : U ⟶ T) (b : W ⟶ U) (k : W ⟶ T) (hk : b ≫ g = k)
    (φ : (modulePullbackPseudofunctor.map (bcMap f g).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map (bcMap f g).op.toLoc).toFunctor.obj M')
    (h : pullHom φ (bcSection f σ hσ U) _ _ rfl rfl = sectionRestrict f σ hσ β g) :
    pullHom (pullHom φ (bcMap f b) (bcMap f k) (bcMap f k) (bcMap_comp_eq f g b k hk)
          (bcMap_comp_eq f g b k hk))
        (bcSection f σ hσ W) _ _ rfl rfl =
      sectionRestrict f σ hσ β k := by
  have hsw : bcSection f σ hσ W ≫ bcMap f b = b.left ≫ bcSection f σ hσ U :=
    bcSection_comp_bcMap f σ hσ b
  have p2 : b.left ≫ (bcSection f σ hσ U ≫ bcMap f g) = bcSection f σ hσ W ≫ bcMap f k :=
    comp_sectionComp f σ hσ g b k hk
  have p1 : (b.left ≫ bcSection f σ hσ U) ≫ bcMap f g = bcSection f σ hσ W ≫ bcMap f k :=
    (Category.assoc _ _ _).trans p2
  calc pullHom (pullHom φ (bcMap f b) (bcMap f k) (bcMap f k) (bcMap_comp_eq f g b k hk)
          (bcMap_comp_eq f g b k hk)) (bcSection f σ hσ W) _ _ rfl rfl
      = pullHom φ (b.left ≫ bcSection f σ hσ U) _ _ p1 p1 :=
        Stacks.Picard.pullHom_pullHom_of_eq φ (bcMap f b) _ _ (bcMap_comp_eq f g b k hk)
          (bcMap_comp_eq f g b k hk) (bcSection f σ hσ W) _ hsw _ _ rfl rfl p1 p1
    _ = pullHom (pullHom φ (bcSection f σ hσ U) _ _ rfl rfl) b.left _ _ p2 p2 :=
        (Stacks.Picard.pullHom_pullHom_of_eq φ (bcSection f σ hσ U) _ _ rfl rfl
          b.left _ rfl _ _ p2 p2 p1 p1).symm
    _ = pullHom (sectionRestrict f σ hσ β g) b.left _ _ p2 p2 := by rw [h]
    _ = sectionRestrict f σ hσ β k := pullHom_sectionRestrict' f σ hσ β g b k hk

/-- **Normalised trivialisations agree after any further pullback.** -/
private theorem pullHom_eq_of_pullHom_section_eq
    (hOiso : ∀ U : Over S, IsIso (bcProj f U).toLRSHom.toHom.c)
    {T : Over S} (L' M' : (bc f T).Modules)
    (hL' : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf (bc f T).ringCatSheaf.2 L')
    (hM' : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf (bc f T).ringCatSheaf.2 M')
    (β : (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map (bcSection f σ hσ T).op.toLoc).toFunctor.obj M')
    {ι : Type*} {U : ι → Over S} (g : ∀ i, U i ⟶ T)
    (ψ : ∀ i, (modulePullbackPseudofunctor.map (bcMap f (g i)).op.toLoc).toFunctor.obj L' ⟶
      (modulePullbackPseudofunctor.map (bcMap f (g i)).op.toLoc).toFunctor.obj M')
    (hψ : ∀ i, pullHom (ψ i) (bcSection f σ hσ (U i)) _ _ rfl rfl =
      sectionRestrict f σ hσ β (g i))
    (etriv : ∀ (V : Over S) (i : ι) (b : V ⟶ U i) (k : V ⟶ T), b ≫ g i = k →
      Nonempty ((modulePullbackPseudofunctor.map (bcMap f k).op.toLoc).toFunctor.obj L' ≅
        (modulePullbackPseudofunctor.map (bcMap f k).op.toLoc).toFunctor.obj M'))
    ⦃Y : Scheme.{u}⦄ (q : Y ⟶ bc f T) ⦃i₁ i₂ : ι⦄
    (a₁ : Y ⟶ bc f (U i₁)) (a₂ : Y ⟶ bc f (U i₂))
    (ha₁ : a₁ ≫ bcMap f (g i₁) = q) (ha₂ : a₂ ≫ bcMap f (g i₂) = q) :
    pullHom (ψ i₁) a₁ q q ha₁ ha₁ = pullHom (ψ i₂) a₂ q q ha₂ ha₂ := by
  let c := overChosenPullback (g i₁) (g i₂)
  let W := c.pullback
  let b₁ := c.p₁
  let b₂ := c.p₂
  have hb : b₁ ≫ g i₁ = b₂ ≫ g i₂ := c.condition
  obtain ⟨eW⟩ := etriv W i₁ b₁ (b₁ ≫ g i₁) rfl
  have hpbbc : IsPullback (bcMap f b₁) (bcMap f b₂) (bcMap f (g i₁)) (bcMap f (g i₂)) :=
    isPullback_bcChosen f (g i₁) (g i₂)
  have hsecW : bcSection f σ hσ W ≫ bcProj f W = 𝟙 _ := bcSection_comp_snd f σ hσ W
  have hkey : pullHom (ψ i₁) (bcMap f b₁) (bcMap f (b₁ ≫ g i₁)) (bcMap f (b₁ ≫ g i₁))
        (bcMap_comp_eq f (g i₁) b₁ _ rfl) (bcMap_comp_eq f (g i₁) b₁ _ rfl) =
      pullHom (ψ i₂) (bcMap f b₂) (bcMap f (b₁ ≫ g i₁)) (bcMap f (b₁ ≫ g i₁))
        (bcMap_comp_eq f (g i₂) b₂ _ hb.symm) (bcMap_comp_eq f (g i₂) b₂ _ hb.symm) := by
    refine (Stacks.Picard.bijective_pullHom_section' (bcMap f (b₁ ≫ g i₁))
      (bcMap f (b₁ ≫ g i₁)) (bcProj f W) (bcSection f σ hσ W) hsecW (hOiso W)
      L' M' hL' hM' eW _ _ rfl rfl).injective ?_
    change pullHom _ (bcSection f σ hσ W) _ _ rfl rfl = pullHom _ (bcSection f σ hσ W) _ _ rfl rfl
    rw [pullHom_section_pullHom_bcMap f σ hσ β (g i₁) b₁ _ rfl (ψ i₁) (hψ i₁),
      pullHom_section_pullHom_bcMap f σ hσ β (g i₂) b₂ _ hb.symm (ψ i₂) (hψ i₂)]
  have hl₁ : hpbbc.lift a₁ a₂ (by rw [ha₁, ha₂]) ≫ bcMap f b₁ = a₁ := hpbbc.lift_fst _ _ _
  have hl₂ : hpbbc.lift a₁ a₂ (by rw [ha₁, ha₂]) ≫ bcMap f b₂ = a₂ := hpbbc.lift_snd _ _ _
  have hq : hpbbc.lift a₁ a₂ (by rw [ha₁, ha₂]) ≫ bcMap f (b₁ ≫ g i₁) = q := by
    rw [← bcMap_comp_eq f (g i₁) b₁ _ rfl, ← Category.assoc, hl₁, ha₁]
  rw [← Stacks.Picard.pullHom_pullHom_of_eq (ψ i₁) (bcMap f b₁) _ _
      (bcMap_comp_eq f (g i₁) b₁ _ rfl) (bcMap_comp_eq f (g i₁) b₁ _ rfl)
      (hpbbc.lift a₁ a₂ (by rw [ha₁, ha₂])) a₁ hl₁ q q hq hq ha₁ ha₁,
    ← Stacks.Picard.pullHom_pullHom_of_eq (ψ i₂) (bcMap f b₂) _ _
      (bcMap_comp_eq f (g i₂) b₂ _ hb.symm) (bcMap_comp_eq f (g i₂) b₂ _ hb.symm)
      (hpbbc.lift a₁ a₂ (by rw [ha₁, ha₂])) a₂ hl₂ q q hq hq ha₂ ha₂,
    hkey]

/-! ### Separatedness -/

/-- **A Picard class of `X_T` killed by `σ_T^*` and by its restriction to every member of a
family of `S`-schemes whose base change is an fpqc covering of `X_T` is zero.** -/
theorem eq_zero_of_section_eq_zero
    (hOiso : ∀ U : Over S, IsIso (bcProj f U).toLRSHom.toHom.c)
    {T : Over S} {ι : Type*} {U : ι → Over S} (g : ∀ i, U i ⟶ T)
    (hfpqc : Presieve.ofArrows (fun i => bc f (U i)) (fun i => bcMap f (g i)) ∈
      Scheme.fpqcPrecoverage.{u} (bc f T))
    (c : Stacks.Picard.ofScheme (bc f T))
    (hc : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c = 0)
    (hloc : ∀ i, Stacks.Picard.schemePullbackClass (bcMap f (g i)) c = 0) :
    c = 0 := by
  classical
  have hLinv : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf (bc f T).ringCatSheaf.2
      (Stacks.Picard.picardRepresentative (bc f T).toRingedSpace c).obj :=
    (Stacks.Picard.picardRepresentative (bc f T).toRingedSpace c).property
  have hOinv : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf (bc f T).ringCatSheaf.2
      (SheafOfModules.unit (bc f T).ringCatSheaf) :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  obtain ⟨β⟩ := Stacks.Picard.nonempty_pullHomIso_of_schemePullbackClass_eq_zero
    (bcSection f σ hσ T) c hc
  have etriv : ∀ (V : Over S) (i : ι) (b : V ⟶ U i) (k : V ⟶ T), b ≫ g i = k →
      Nonempty ((modulePullbackPseudofunctor.map (bcMap f k).op.toLoc).toFunctor.obj
          (Stacks.Picard.picardRepresentative (bc f T).toRingedSpace c).obj ≅
        (modulePullbackPseudofunctor.map (bcMap f k).op.toLoc).toFunctor.obj
          (SheafOfModules.unit (bc f T).ringCatSheaf)) := by
    intro V i b k hk
    refine Stacks.Picard.nonempty_pullHomIso_of_schemePullbackClass_eq_zero (bcMap f k) c ?_
    rw [← bcMap_comp_eq f (g i) b k hk, ← Stacks.Picard.schemePullbackClass_comp, hloc i]
    exact map_zero (Stacks.Picard.schemePullbackClassHom (bcMap f b))
  have hnorm : ∀ i : ι, ∃ ψ : (modulePullbackPseudofunctor.map
          (bcMap f (g i)).op.toLoc).toFunctor.obj
            (Stacks.Picard.picardRepresentative (bc f T).toRingedSpace c).obj ≅
        (modulePullbackPseudofunctor.map (bcMap f (g i)).op.toLoc).toFunctor.obj
            (SheafOfModules.unit (bc f T).ringCatSheaf),
      pullHom ψ.hom (bcSection f σ hσ (U i)) _ _ rfl rfl =
        sectionRestrict f σ hσ β.hom (g i) := fun i =>
    exists_pullHom_eq_sectionRestrict f σ hσ hOiso _ _ hLinv hOinv β (g i)
      (etriv (U i) i (𝟙 _) (g i) (Category.id_comp _)).some
  choose ψ hψ using hnorm
  have hLqc := Stacks.Picard.isQuasicoherent_of_isInvertible _ hLinv
  have hOqc := Stacks.Picard.isQuasicoherent_of_isInvertible _ hOinv
  rw [Stacks.Picard.eq_zero_iff_nonempty_iso_unit]
  exact Stacks.Picard.nonempty_iso_of_pullHom_hom_eq (fun i => bcMap f (g i))
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hLqc hOqc)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hOqc hLqc)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hLqc hLqc)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hOqc hOqc)
    ψ (pullHom_eq_of_pullHom_section_eq f σ hσ hOiso _ _ hLinv hOinv β.hom g
      (fun i => (ψ i).hom) hψ etriv)

/-- Two Picard classes of `X_T` with the same pullback along `σ_T` that agree on every member
of a family whose base change is an fpqc covering are equal. -/
theorem eq_of_section_eq
    (hOiso : ∀ U : Over S, IsIso (bcProj f U).toLRSHom.toHom.c)
    {T : Over S} {ι : Type*} {U : ι → Over S} (g : ∀ i, U i ⟶ T)
    (hfpqc : Presieve.ofArrows (fun i => bc f (U i)) (fun i => bcMap f (g i)) ∈
      Scheme.fpqcPrecoverage.{u} (bc f T))
    (c c' : Stacks.Picard.ofScheme (bc f T))
    (hc : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c =
      Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c')
    (hloc : ∀ i, Stacks.Picard.schemePullbackClass (bcMap f (g i)) c =
      Stacks.Picard.schemePullbackClass (bcMap f (g i)) c') :
    c = c' := by
  have key : ∀ {Y : Scheme.{u}} (h : Y ⟶ bc f T),
      Stacks.Picard.schemePullbackClass h c = Stacks.Picard.schemePullbackClass h c' →
        Stacks.Picard.schemePullbackClass h (c - c') = 0 := fun h e => by
    change Stacks.Picard.schemePullbackClassHom h (c - c') = 0
    rwa [map_sub, sub_eq_zero]
  exact sub_eq_zero.1 (eq_zero_of_section_eq_zero f σ hσ hOiso g hfpqc _ (key _ hc)
    fun i => key _ (hloc i))

/-! ### Gluing -/

/-- A trivialisation along the induced section of a Picard class of `X_U` that dies on that
restriction, with the structure sheaf of the base pulled back along `U ⟶ T` as target. -/
private theorem nonempty_sectionTrivialization {T U : Over S} (g : U ⟶ T)
    (x : Stacks.Picard.ofScheme (bc f U))
    (hx : Stacks.Picard.schemePullbackClass (bcSection f σ hσ U) x = 0) :
    Nonempty ((modulePullbackPseudofunctor.map (bcSection f σ hσ U).op.toLoc).toFunctor.obj
        (Stacks.Picard.picardRepresentative (bc f U).toRingedSpace x).obj ≅
      (modulePullbackPseudofunctor.map g.left.op.toLoc).toFunctor.obj
        (SheafOfModules.unit T.left.ringCatSheaf)) :=
  ((Stacks.Picard.schemePullbackClass_eq_zero_iff_nonempty_iso_unit
    (bcSection f σ hσ U) x).1 hx).map
      (fun e => e ≪≫ (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g.left).symm)

/-- Two Picard classes whose pullbacks agree have isomorphic pulled-back representatives. -/
private theorem nonempty_iso_pullback_representative {V U U' : Over S}
    (a : V ⟶ U) (b : V ⟶ U') (xi : Stacks.Picard.ofScheme (bc f U))
    (xj : Stacks.Picard.ofScheme (bc f U'))
    (h : Stacks.Picard.schemePullbackClass (bcMap f a) xi =
      Stacks.Picard.schemePullbackClass (bcMap f b) xj) :
    Nonempty ((modulePullbackPseudofunctor.map (bcMap f a).op.toLoc).toFunctor.obj
        (Stacks.Picard.picardRepresentative (bc f U).toRingedSpace xi).obj ≅
      (modulePullbackPseudofunctor.map (bcMap f b).op.toLoc).toFunctor.obj
        (Stacks.Picard.picardRepresentative (bc f U').toRingedSpace xj).obj) := by
  refine (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _
    (Stacks.RingedSpace.modulePullback_isInvertible_of (bcMap f a).toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative (bc f U).toRingedSpace xi).property)
    (Stacks.RingedSpace.modulePullback_isInvertible_of (bcMap f b).toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative (bc f U').toRingedSpace xj).property)).1 ?_
  refine ((Stacks.Picard.pullbackClass_classOf (bcMap f a).toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative (bc f U).toRingedSpace xi).property).symm.trans
    ?_).trans (Stacks.Picard.pullbackClass_classOf (bcMap f b).toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative (bc f U').toRingedSpace xj).property)
  rwa [Stacks.Picard.classOf_picardRepresentative, Stacks.Picard.classOf_picardRepresentative]

/-- **The normalised local classes assemble into a quasi-coherent descent datum.** -/
private theorem exists_quasicoherentDescentData
    (hOiso : ∀ U : Over S, IsIso (bcProj f U).toLRSHom.toHom.c)
    {T : Over S} {ι : Type (u + 1)} {U : ι → Over S} (g : ∀ i, U i ⟶ T)
    (x : ∀ i, Stacks.Picard.ofScheme (bc f (U i)))
    (hx0 : ∀ i, Stacks.Picard.schemePullbackClass (bcSection f σ hσ (U i)) (x i) = 0)
    (hagree : ∀ (V : Over S) (i j : ι) (a : V ⟶ U i) (b : V ⟶ U j), a ≫ g i = b ≫ g j →
      Stacks.Picard.schemePullbackClass (bcMap f a) (x i) =
        Stacks.Picard.schemePullbackClass (bcMap f b) (x j)) :
    ∃ D : QuasicoherentDescentData (bcHypercover f g).f,
      ∀ i, Nonempty (D.component i ≅
        (Stacks.Picard.picardRepresentative (bc f (U i)).toRingedSpace (x i)).obj) := by
  classical
  have hLinv : ∀ i, Stacks.SheafOfModules.IsInvertible (bc f (U i)).presheaf
      (bc f (U i)).ringCatSheaf.2
      (Stacks.Picard.picardRepresentative (bc f (U i)).toRingedSpace (x i)).obj := fun i =>
    (Stacks.Picard.picardRepresentative (bc f (U i)).toRingedSpace (x i)).property
  refine ⟨⟨(Pseudofunctor.DescentData'.toDescentDataFunctor modulePullbackPseudofunctor
      (fun i j => Stacks.Picard.mapChosenPullback (bcFunctor f)
        (overChosenPullback (g i) (g j)) (isPullback_bcChosen f (g i) (g j)))
      (Stacks.Picard.mapChosenPullback₃ (bcFunctor f)
        (fun i j => overChosenPullback (g i) (g j))
        (fun i j k => overChosenPullback₃ (g i) (g j) (g k))
        (fun i j => isPullback_bcChosen f (g i) (g j))
        (fun i j k => isPullback_bcChosen₃ f (g i) (g j) (g k)))).obj
      (Stacks.Picard.diagramDescentData (F := modulePullbackPseudofunctor) (bcFunctor f)
        (fun i j => overChosenPullback (g i) (g j))
        (fun i j k => overChosenPullback₃ (g i) (g j) (g k))
        (fun i j => isPullback_bcChosen f (g i) (g j))
        (fun i j k => isPullback_bcChosen₃ f (g i) (g j) (g k))
        (fun i => (Stacks.Picard.picardRepresentative (bc f (U i)).toRingedSpace (x i)).obj)
        (fun {V} q {i j} a b ha hb =>
          Stacks.Picard.normalizedHom (F := modulePullbackPseudofunctor)
            (Over.forget S) (bcFunctor f) (bcSectionNatTrans f σ hσ) g
            (fun i => (Stacks.Picard.picardRepresentative (bc f (U i)).toRingedSpace (x i)).obj)
            (SheafOfModules.unit T.left.ringCatSheaf)
            (fun i => (nonempty_sectionTrivialization f σ hσ (g i) (x i) (hx0 i)).some)
            (fun {V'} q' {i' j'} a' b' ha' hb' =>
              Stacks.Picard.bijective_pullHom_section' (bcMap f a') (bcMap f b')
                (bcProj f V') (bcSection f σ hσ V') (bcSection_comp_snd f σ hσ V') (hOiso V')
                _ _ (hLinv i') (hLinv j')
                (nonempty_iso_pullback_representative f a' b' (x i') (x j')
                  (hagree V' i' j' a' b' (ha'.trans hb'.symm))).some _ _ rfl rfl)
            q a b ha hb)
        (fun {V} q {i} a ha => Stacks.Picard.normalizedHom_self _ _ _ _ _ _ _ _ q a ha)
        (fun {V} q {i j k} a b c ha hb hc =>
          Stacks.Picard.normalizedHom_comp _ _ _ _ _ _ _ _ q a b c ha hb hc)
        (fun {V W} r q {i j} a b ha hb =>
          Stacks.Picard.normalizedHom_pull _ _ _ _ _ _ _ _ r q a b ha hb)),
    fun i => Stacks.Picard.isQuasicoherent_of_isInvertible _ (hLinv i)⟩,
    fun i => ⟨Iso.refl _⟩⟩

/-- **Gluing.** Picard classes on the base changes of the members of a family of `S`-schemes
over `T` whose base change is an fpqc covering of `X_T`, killed by the induced sections and
agreeing after every further pullback, are the restrictions of one Picard class of `X_T`. -/
theorem exists_glue
    (hOiso : ∀ U : Over S, IsIso (bcProj f U).toLRSHom.toHom.c)
    {T : Over S} {ι : Type (u + 1)} {U : ι → Over S} (g : ∀ i, U i ⟶ T)
    (hfpqc : Presieve.ofArrows (fun i => bc f (U i)) (fun i => bcMap f (g i)) ∈
      Scheme.fpqcPrecoverage.{u} (bc f T))
    (x : ∀ i, Stacks.Picard.ofScheme (bc f (U i)))
    (hx0 : ∀ i, Stacks.Picard.schemePullbackClass (bcSection f σ hσ (U i)) (x i) = 0)
    (hagree : ∀ (V : Over S) (i j : ι) (a : V ⟶ U i) (b : V ⟶ U j), a ≫ g i = b ≫ g j →
      Stacks.Picard.schemePullbackClass (bcMap f a) (x i) =
        Stacks.Picard.schemePullbackClass (bcMap f b) (x j)) :
    ∃ c : Stacks.Picard.ofScheme (bc f T),
      ∀ i, Stacks.Picard.schemePullbackClass (bcMap f (g i)) c = x i := by
  classical
  obtain ⟨D, hD⟩ := exists_quasicoherentDescentData f σ hσ hOiso g x hx0 hagree
  have h𝒰 : (bcHypercover f g).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} (bc f T) := hfpqc
  obtain ⟨M, hMqc, hMiso⟩ :=
    Stacks.Picard.exists_isQuasicoherent_nonempty_iso_component (bcHypercover f g) h𝒰 D
  have hMinv : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf (bc f T).ringCatSheaf.2 M := by
    refine Stacks.Picard.isInvertible_of_pullback_fpqcCover M hMqc ⟨bcHypercover f g, h𝒰⟩
      fun i => Stacks.Picard.isInvertible_of_iso (((hMiso i).some.trans (hD i).some).symm)
        (Stacks.Picard.picardRepresentative (bc f (U i)).toRingedSpace (x i)).property
  refine ⟨Stacks.SheafOfModules.picardClass (bc f T).presheaf (bc f T).ringCatSheaf.2 M hMinv,
    fun i => ?_⟩
  exact (Stacks.Picard.pullbackClass_classOf (bcMap f (g i)).toLRSHom.toShHom M hMinv).trans
    (((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
        ⟨(hMiso i).some.trans (hD i).some⟩).trans
      (Stacks.Picard.classOf_picardRepresentative (bc f (U i)).toRingedSpace (x i)))

end Stacks.RigidifiedPicard

end
