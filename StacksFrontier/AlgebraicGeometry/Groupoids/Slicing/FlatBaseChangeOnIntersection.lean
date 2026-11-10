module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.FunctionsOnIntersection
public import StacksFrontier.CategoryTheory.Limits.ColimitOfPushouts

/-!
# Flat base change for the functions on an intersection of quasi-compact opens

Let

```
  X ---k---→ Spec R
  |            |
  p            g
  ↓            ↓
  Y ---πY--→ Spec A
```

be a Cartesian square of schemes with `Y` quasi-separated and `g` flat, and let
`E = ⋂ i, V i` be an intersection of a nonempty family of quasi-compact opens of `Y`. Then the
functions on the preimage `p⁻¹(E)` are the base change of the functions on `E`:
`Γ(p⁻¹E, 𝒪_X|_{p⁻¹E}) = Γ(E, 𝒪_Y|_E) ⊗_A R`, in the form of a pushout square of commutative
rings.

## Main definitions

* `AlgebraicGeometry.Scheme.topToSubset` is the restriction of a global function of a scheme to a
  subset, that is to the inverse image of the structure sheaf on that subset.
* `AlgebraicGeometry.preimageIntersectionIndex` is the functor between the reverse-inclusion index
  categories of a family of opens and of the family of its preimages under a morphism.

## Main results

* `AlgebraicGeometry.Scheme.presheaf_map_stageToSubset` and
  `AlgebraicGeometry.Scheme.appTop_presheaf_map_stageToSubset`: restricting a global function to a
  member of the family and then to the subset is restricting it to the subset.
* `AlgebraicGeometry.isPushout_appLE_of_flat`: the square of sections over one quasi-compact open
  of `Y` and over its preimage is a pushout.
* `AlgebraicGeometry.flat_resLE_top`: flatness survives restricting a morphism to the total opens
  of its source and target.
* `AlgebraicGeometry.resLE_appTop_topIso`: the global sections of a restriction `resLE` are the
  sections `appLE`, up to the identifications of the global sections of open subschemes.
* `AlgebraicGeometry.final_preimageIntersectionIndex`: the functor between the two index
  categories is final.
* `AlgebraicGeometry.isPushout_sectionsRingOnSubset_of_flat_of_directed` and
  `AlgebraicGeometry.isPushout_sectionsRingOnSubset_of_flat`: the functions on the preimage of an
  intersection of a nonempty family of quasi-compact opens are the base change of the functions
  on the intersection, first for a family directed under reverse inclusion and then for an
  arbitrary nonempty family.

## References

* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 0APH](https://stacks.math.columbia.edu/tag/0APH)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Restricting a global function to a subset -/

/-- The restriction of a global function of a scheme to a subset, that is to the inverse image of
the structure sheaf on that subset. -/
def Scheme.topToSubset (X : Scheme.{u}) (E : Set X) : Γ(X, ⊤) ⟶ X.sectionsRingOnSubset E :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (Stacks.subsetInclusion (TopCat.of X) E)).unit.app X.toSheafedSpace.sheaf).hom.app
      (op ⊤)) ≫
    ((TopCat.Sheaf.pullback CommRingCat.{u} (Stacks.subsetInclusion (TopCat.of X) E)).obj
      X.toSheafedSpace.sheaf).obj.map
        (homOfLE (by intro x _; trivial : (⊤ : TopologicalSpace.Opens E) ≤
          (TopologicalSpace.Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj ⊤)).op

/-- Restricting a global function to a stage of a family of opens containing a subset and then to
the subset is the restriction of that global function to the subset. -/
lemma Scheme.presheaf_map_stageToSubset (X : Scheme.{u}) {I : Type u} (U : I → X.Opens)
    (E : Set X) (hE : ∀ i, E ⊆ U i) (i : intersectionIndex U) (h : U i.val ≤ (⊤ : X.Opens)) :
    X.presheaf.map (homOfLE h).op ≫ X.stageToSubset U E hE i = X.topToSubset E := by
  let incl := Stacks.subsetInclusion (TopCat.of X) E
  let P := ((TopCat.Sheaf.pullback CommRingCat.{u} incl).obj X.toSheafedSpace.sheaf).obj
  let η := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} incl).unit.app
    X.toSheafedSpace.sheaf).hom
  let Om := TopologicalSpace.Opens.map incl
  let a : (op (⊤ : X.Opens) : (TopologicalSpace.Opens X)ᵒᵖ) ⟶ op (U i.val) := (homOfLE h).op
  let a' : (op (Om.obj ⊤) : (TopologicalSpace.Opens E)ᵒᵖ) ⟶ op (Om.obj (U i.val)) :=
    (Om.map a.unop).op
  let bi : (op (Om.obj (U i.val)) : (TopologicalSpace.Opens E)ᵒᵖ) ⟶ op ⊤ :=
    (homOfLE (by intro x hx; exact hE i.val x.2)).op
  let bt : (op (Om.obj (⊤ : X.Opens)) : (TopologicalSpace.Opens E)ᵒᵖ) ⟶ op ⊤ :=
    (homOfLE (by intro x _; trivial)).op
  change X.toSheafedSpace.sheaf.obj.map a ≫ η.app (op (U i.val)) ≫ P.map bi =
    η.app (op ⊤) ≫ P.map bt
  have step1 : X.toSheafedSpace.sheaf.obj.map a ≫ η.app (op (U i.val)) =
      η.app (op ⊤) ≫ P.map a' := η.naturality a
  have step2 : P.map a' ≫ P.map bi = P.map bt := by
    rw [← P.map_comp, Subsingleton.elim (a' ≫ bi) bt]
  calc X.toSheafedSpace.sheaf.obj.map a ≫ η.app (op (U i.val)) ≫ P.map bi
      = (X.toSheafedSpace.sheaf.obj.map a ≫ η.app (op (U i.val))) ≫ P.map bi :=
        (Category.assoc _ _ _).symm
    _ = (η.app (op ⊤) ≫ P.map a') ≫ P.map bi := congrArg (· ≫ P.map bi) step1
    _ = η.app (op ⊤) ≫ P.map a' ≫ P.map bi := Category.assoc _ _ _
    _ = η.app (op ⊤) ≫ P.map bt := congrArg (η.app (op ⊤) ≫ ·) step2

/-- Pulling a global function back along a morphism, restricting it to a stage of a family of
opens containing a subset and then restricting it to the subset is the restriction to the subset
of the pullback of that global function. -/
lemma Scheme.appTop_presheaf_map_stageToSubset {X Z : Scheme.{u}} (f : X ⟶ Z) {I : Type u}
    (U : I → X.Opens) (E : Set X) (hE : ∀ i, E ⊆ U i) (i : intersectionIndex U)
    (h : U i.val ≤ (⊤ : X.Opens)) :
    (f.appTop ≫ X.presheaf.map (homOfLE h).op) ≫ X.stageToSubset U E hE i =
      f.appTop ≫ X.topToSubset E :=
  (Category.assoc _ _ _).trans
    (congrArg (f.appTop ≫ ·) (X.presheaf_map_stageToSubset U E hE i h))

/-! ### Flat base change over one quasi-compact open -/

/-- Flatness of a morphism survives the restriction of its source and target to their own total
opens. -/
lemma flat_resLE_top {X Y : Scheme.{u}} (g : X ⟶ Y) [Flat g]
    (e : (⊤ : X.Opens) ≤ g ⁻¹ᵁ (⊤ : Y.Opens)) : Flat (g.resLE ⊤ ⊤ e) := by
  have h : g.resLE (⊤ : Y.Opens) (⊤ : X.Opens) e = X.topIso.hom ≫ g ≫ Y.topIso.inv := by
    rw [← cancel_mono Y.topIso.hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Scheme.topIso_hom, Scheme.topIso_hom, Scheme.Hom.resLE_comp_ι]
  rw [h]
  infer_instance

/-- The global sections of a restriction `resLE` are the sections `appLE`, transported along the
isomorphisms identifying the global sections of an open subscheme with the sections on that
open. -/
lemma resLE_appTop_topIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) :
    (f.resLE U V e).appTop ≫ V.topIso.hom = U.topIso.hom ≫ f.appLE U V e :=
  (arrowResLEAppIso f U V e).hom.w.symm

/-- In a Cartesian square
```
  X ---k---→ T
  |          |
  p          g
  ↓          ↓
  Y ---πY--→ S
```
with `S` and `T` affine, `g` flat and `Y` quasi-separated, and for a quasi-compact open `U` of
`Y`, the square of sections over `U` and over its preimage is a pushout of rings, that is
`Γ(X, p⁻¹U) = Γ(Y, U) ⊗_{Γ(S, ⊤)} Γ(T, ⊤)`. -/
theorem isPushout_appLE_of_flat {S T Y X : Scheme.{u}} [IsAffine S] [IsAffine T]
    {πY : Y ⟶ S} {g : T ⟶ S} {p : X ⟶ Y} {k : X ⟶ T} (H : IsPullback p k πY g) [Flat g]
    [QuasiSeparatedSpace Y] (U : Y.Opens) (hU : IsCompact (U : Set Y)) :
    IsPushout (πY.appTop ≫ Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) g.appTop
      (p.appLE U (p ⁻¹ᵁ U) le_rfl)
      (k.appTop ≫ X.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ U ≤ ⊤)).op) := by
  have eT : (⊤ : T.Opens) ≤ g ⁻¹ᵁ (⊤ : S.Opens) := le_of_eq (g.preimage_top).symm
  have eU : U ≤ πY ⁻¹ᵁ (⊤ : S.Opens) := le_top.trans (le_of_eq (πY.preimage_top).symm)
  have eV : p ⁻¹ᵁ U ≤ k ⁻¹ᵁ (⊤ : T.Opens) := le_top.trans (le_of_eq (k.preimage_top).symm)
  have hUY : p ⁻¹ᵁ U = p ⁻¹ᵁ U ⊓ k ⁻¹ᵁ (⊤ : T.Opens) := by
    simp only [Scheme.Hom.preimage_top, inf_top_eq]
  have HR := Scheme.Hom.isPullback_resLE H (US := (⊤ : S.Opens)) (UT := (⊤ : T.Opens))
    (UX := U) eT eU hUY
  have : IsAffine (⊤ : S.Opens).toScheme := isAffineOpen_top S
  have : IsAffine (⊤ : T.Opens).toScheme := isAffineOpen_top T
  have : Flat (g.resLE (⊤ : S.Opens) (⊤ : T.Opens) eT) := flat_resLE_top g eT
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme := QuasiSeparatedSpace.of_isOpenEmbedding U.isOpenEmbedding
  refine (isPushout_appTop_of_flat HR).of_iso (⊤ : S.Opens).topIso U.topIso
    (⊤ : T.Opens).topIso (p ⁻¹ᵁ U).topIso (resLE_appTop_topIso πY ⊤ U eU) ?_
    (resLE_appTop_topIso p U (p ⁻¹ᵁ U) _) (resLE_appTop_topIso k ⊤ (p ⁻¹ᵁ U) eV)
  exact (resLE_appTop_topIso g ⊤ ⊤ eT).trans
    (congrArg ((⊤ : S.Opens).topIso.hom ≫ ·) (Stacks.AffineAlgebraEquivalence.appLE_top_top g eT))

/-! ### The index categories of a family and of the family of its preimages -/

/-- The functor from the reverse-inclusion index category of a family of opens to that of the
family of its preimages under a morphism, sending each member to its preimage. -/
def preimageIntersectionIndex {X Y : Scheme.{u}} (p : X ⟶ Y) {I : Type u} (V : I → Y.Opens) :
    intersectionIndex V ⥤ intersectionIndex (fun i ↦ p ⁻¹ᵁ V i) where
  obj i := ⟨i.val⟩
  map {i j} f := homOfLE (show p ⁻¹ᵁ V j.val ≤ p ⁻¹ᵁ V i.val from p.preimage_mono f.le)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- For a nonempty family of opens directed under reverse inclusion, the functor from its index
category to that of the family of its preimages is final. -/
lemma final_preimageIntersectionIndex {X Y : Scheme.{u}} (p : X ⟶ Y) {I : Type u} [Nonempty I]
    (V : I → Y.Opens) (hdir : ∀ i j, ∃ l, (V l : Set Y) ⊆ V i ∩ V j) :
    (preimageIntersectionIndex p V).Final := by
  have : IsFiltered (intersectionIndex V) := filtered_intersectionIndex V hdir
  exact Functor.final_of_exists_of_isFiltered _ (fun d ↦ ⟨⟨d.val⟩, ⟨𝟙 _⟩⟩)
    fun {_ c} _ _ ↦ ⟨c, 𝟙 c, Subsingleton.elim _ _⟩


/-! ### Flat base change for the functions on an intersection -/

/-- In a Cartesian square
```
  X ---k---→ Spec R
  |            |
  p            g
  ↓            ↓
  Y ---πY--→ Spec A
```
with `Y` quasi-separated and `g` flat, if `E` is the intersection of a nonempty family of
quasi-compact opens of `Y` which is directed under reverse inclusion, then the functions on
`p⁻¹E` are the base change of the functions on `E` along `Γ(Spec A, ⊤) ⟶ Γ(Spec R, ⊤)`. -/
theorem isPushout_sectionsRingOnSubset_of_flat_of_directed {A R : CommRingCat.{u}}
    {Y X : Scheme.{u}} {πY : Y ⟶ Spec A} {g : Spec R ⟶ Spec A} {p : X ⟶ Y} {k : X ⟶ Spec R}
    (H : IsPullback p k πY g) [Flat g] [QuasiSeparatedSpace Y] {I : Type u} [Nonempty I]
    (V : I → Y.Opens) (hV : ∀ i, IsCompact (V i : Set Y))
    (hdir : ∀ i j, ∃ l, (V l : Set Y) ⊆ V i ∩ V j)
    (E : Set Y) (hE : E = ⋂ i, (V i : Set Y)) :
    ∃ w : Y.sectionsRingOnSubset E ⟶ X.sectionsRingOnSubset (p.base ⁻¹' E),
      IsPushout (πY.appTop ≫ Y.topToSubset E) g.appTop w
          (k.appTop ≫ X.topToSubset (p.base ⁻¹' E)) ∧
        ∀ i : I,
          Y.stageToSubset V E (fun j ↦ hE ▸ Set.iInter_subset _ j) ⟨i⟩ ≫ w =
            p.appLE (V i) (p ⁻¹ᵁ V i) le_rfl ≫
              X.stageToSubset (fun j ↦ p ⁻¹ᵁ V j) (p.base ⁻¹' E)
                (fun j ↦ hE ▸ Set.preimage_mono (Set.iInter_subset _ j)) ⟨i⟩ := by
  classical
  have hEY : ∀ j, E ⊆ (V j : Set Y) := fun j ↦ hE ▸ Set.iInter_subset _ j
  have hEX : ∀ j, p.base ⁻¹' E ⊆ ((p ⁻¹ᵁ V j : X.Opens) : Set X) :=
    fun j ↦ hE ▸ Set.preimage_mono (Set.iInter_subset _ j)
  have : IsAffineHom p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback H.flip inferInstance
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace p).mp inferInstance
  have hVX : ∀ i, IsCompact ((p ⁻¹ᵁ V i : X.Opens) : Set X) := fun i ↦
    QuasiCompact.isCompact_preimage (f := p) _ (V i).isOpen (hV i)
  have hdirX : ∀ i j, ∃ l, ((p ⁻¹ᵁ V l : X.Opens) : Set X) ⊆
      ((p ⁻¹ᵁ V i : X.Opens) : Set X) ∩ ((p ⁻¹ᵁ V j : X.Opens) : Set X) :=
    fun i j ↦ (hdir i j).imp fun _ hl _ hx ↦ hl hx
  have hEX' : p.base ⁻¹' E = ⋂ i, ((p ⁻¹ᵁ V i : X.Opens) : Set X) := by
    rw [hE, Set.preimage_iInter]
    rfl
  obtain ⟨eY, heY⟩ := colimit_sectionsRing_iso_sectionsRingOnSubset Y V hV hdir E hE
  obtain ⟨eX, heX⟩ := colimit_sectionsRing_iso_sectionsRingOnSubset X (fun i ↦ p ⁻¹ᵁ V i)
    hVX hdirX (p.base ⁻¹' E) hEX'
  let DY := Scheme.sectionsRingDiagram Y V
  let DX := Scheme.sectionsRingDiagram X (fun i ↦ p ⁻¹ᵁ V i)
  let F := preimageIntersectionIndex p V
  have : F.Final := final_preimageIntersectionIndex p V hdir
  let cY : Cocone DY := (colimit.cocone DY).extend eY.hom
  have hcY : IsColimit cY := (colimit.isColimit DY).extendIso eY.hom
  let cX : Cocone DX := (colimit.cocone DX).extend eX.hom
  have hcX : IsColimit cX := (colimit.isColimit DX).extendIso eX.hom
  have hc₂ : IsColimit (cX.whisker F) := (Functor.Final.isColimitWhiskerEquiv F cX).symm hcX
  let α : ∀ j : intersectionIndex V, Γ(Spec A, ⊤) ⟶ DY.obj j := fun j ↦
    πY.appTop ≫ Y.presheaf.map (homOfLE (le_top : V j.val ≤ ⊤)).op
  let β : ∀ j : intersectionIndex V, Γ(Spec R, ⊤) ⟶ (F ⋙ DX).obj j := fun j ↦
    k.appTop ≫ X.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V j.val ≤ ⊤)).op
  let τ : ∀ j : intersectionIndex V, DY.obj j ⟶ (F ⋙ DX).obj j := fun j ↦
    p.appLE (V j.val) (p ⁻¹ᵁ V j.val) le_rfl
  have hβ : ∀ {i j : intersectionIndex V} (f : i ⟶ j), β i ≫ (F ⋙ DX).map f = β j :=
    fun _ ↦ Scheme.Hom.appLE_map k _ _
  have hτ : ∀ {i j : intersectionIndex V} (f : i ⟶ j),
      τ i ≫ (F ⋙ DX).map f = DY.map f ≫ τ j :=
    fun _ ↦ (Scheme.Hom.appLE_map p _ _).trans (Scheme.Hom.map_appLE p _ _).symm
  let c₂ := cX.whisker F
  have hnat₂ : ∀ {i j : intersectionIndex V} (f : i ⟶ j),
      DY.map f ≫ τ j ≫ c₂.ι.app j = τ i ≫ c₂.ι.app i := by
    intro i j f
    calc DY.map f ≫ τ j ≫ c₂.ι.app j = (DY.map f ≫ τ j) ≫ c₂.ι.app j :=
          (Category.assoc _ _ _).symm
      _ = (τ i ≫ (F ⋙ DX).map f) ≫ c₂.ι.app j := congrArg (· ≫ c₂.ι.app j) (hτ f).symm
      _ = τ i ≫ (F ⋙ DX).map f ≫ c₂.ι.app j := Category.assoc _ _ _
      _ = τ i ≫ c₂.ι.app i := congrArg (τ i ≫ ·) (c₂.w f)
  let cocW : Cocone DY :=
    { pt := c₂.pt
      ι :=
        { app := fun j ↦ τ j ≫ c₂.ι.app j
          naturality := fun i j f ↦ (hnat₂ f).trans (Category.comp_id _).symm } }
  let w := hcY.desc cocW
  have hw : ∀ j, cY.ι.app j ≫ w = τ j ≫ c₂.ι.app j := fun j ↦ hcY.fac _ j
  have hcYι : ∀ j, cY.ι.app j = Y.stageToSubset V E hEY j := fun j ↦ heY j
  have hcXι : ∀ j : intersectionIndex V, c₂.ι.app j =
      X.stageToSubset (fun i ↦ p ⁻¹ᵁ V i) (p.base ⁻¹' E) hEX ⟨j.val⟩ := fun j ↦ heX ⟨j.val⟩
  refine ⟨w, ?_, fun i ↦ ((congrArg (· ≫ w) (hcYι ⟨i⟩)).symm.trans (hw ⟨i⟩)).trans
    (congrArg (τ ⟨i⟩ ≫ ·) (hcXι ⟨i⟩))⟩
  refine IsPushout.of_colimit_of_isPushout g.appTop α β τ ?_ hβ hτ ?_ hcY hc₂ ?_ ?_ hw
  · exact fun _ ↦ Scheme.Hom.appLE_map πY _ _
  · exact fun j ↦ isPushout_appLE_of_flat H (V j.val) (hV j.val)
  · intro j
    exact (congrArg (α j ≫ ·) (hcYι j)).trans
      (Y.appTop_presheaf_map_stageToSubset πY V E hEY j le_top)
  · intro j
    exact (congrArg (β j ≫ ·) (hcXι j)).trans
      (X.appTop_presheaf_map_stageToSubset k (fun i ↦ p ⁻¹ᵁ V i) (p.base ⁻¹' E) hEX ⟨j.val⟩ le_top)

/-- Let
```
  X ---k---→ Spec R
  |            |
  p            g
  ↓            ↓
  Y ---πY--→ Spec A
```
be a Cartesian diagram of schemes, let `E ⊆ Y` be an intersection of a nonempty family of
quasi-compact opens of `Y`, and suppose that `Y` is quasi-separated and that `g` is flat. Then
```
Γ(p⁻¹E, 𝒪_X|_{p⁻¹E}) = Γ(E, 𝒪_Y|_E) ⊗_{Γ(Spec A, ⊤)} Γ(Spec R, ⊤) :
```
the square formed by the restrictions of the global functions of `Spec A` and of `Spec R` to `E`
and to `p⁻¹E` is a pushout of rings.

The comparison morphism `Γ(E, 𝒪_Y|_E) ⟶ Γ(p⁻¹E, 𝒪_X|_{p⁻¹E})` is produced by the statement and
characterized by the second conjunct: it agrees with the restriction along `p` on each member of
the given family. -/
@[stacks 0APJ]
theorem isPushout_sectionsRingOnSubset_of_flat {A R : CommRingCat.{u}} {Y X : Scheme.{u}}
    {πY : Y ⟶ Spec A} {g : Spec R ⟶ Spec A} {p : X ⟶ Y} {k : X ⟶ Spec R}
    (H : IsPullback p k πY g) [Flat g] [QuasiSeparatedSpace Y] {I : Type u} [Nonempty I]
    (V : I → Y.Opens) (hV : ∀ i, IsCompact (V i : Set Y))
    (E : Set Y) (hE : E = ⋂ i, (V i : Set Y)) :
    ∃ w : Y.sectionsRingOnSubset E ⟶ X.sectionsRingOnSubset (p.base ⁻¹' E),
      IsPushout (πY.appTop ≫ Y.topToSubset E) g.appTop w
          (k.appTop ≫ X.topToSubset (p.base ⁻¹' E)) ∧
        ∀ i : I,
          Y.stageToSubset V E (fun j ↦ hE ▸ Set.iInter_subset _ j) ⟨i⟩ ≫ w =
            p.appLE (V i) (p ⁻¹ᵁ V i) le_rfl ≫
              X.stageToSubset (fun j ↦ p ⁻¹ᵁ V j) (p.base ⁻¹' E)
                (fun j ↦ hE ▸ Set.preimage_mono (Set.iInter_subset _ j)) ⟨i⟩ := by
  classical
  have hEY : ∀ j, E ⊆ (V j : Set Y) := fun j ↦ hE ▸ Set.iInter_subset _ j
  let J : Type u := { U : Y.Opens // IsCompact (U : Set Y) ∧ E ⊆ (U : Set Y) }
  have : Nonempty J := ⟨⟨V (Classical.arbitrary I), hV _, hEY _⟩⟩
  have hJV : ∀ j : J, IsCompact ((j.1 : Y.Opens) : Set Y) := fun j ↦ j.2.1
  have hJdir : ∀ i j : J, ∃ l : J, ((l.1 : Y.Opens) : Set Y) ⊆
      ((i.1 : Y.Opens) : Set Y) ∩ ((j.1 : Y.Opens) : Set Y) := fun i j ↦
    ⟨⟨i.1 ⊓ j.1, i.2.1.inter_of_isOpen j.2.1 i.1.isOpen j.1.isOpen,
      Set.subset_inter i.2.2 j.2.2⟩, le_rfl⟩
  have hJE : E = ⋂ j : J, ((j.1 : Y.Opens) : Set Y) := by
    refine (Set.subset_iInter fun j ↦ j.2.2).antisymm fun x hx ↦ ?_
    rw [hE]
    exact Set.mem_iInter.mpr fun i ↦ Set.mem_iInter.mp hx ⟨V i, hV i, hEY i⟩
  obtain ⟨w, hpush, hstage⟩ :=
    isPushout_sectionsRingOnSubset_of_flat_of_directed H (fun j : J ↦ j.1) hJV hJdir E hJE
  exact ⟨w, hpush, fun i ↦ hstage ⟨V i, hV i, hEY i⟩⟩

end AlgebraicGeometry

end

end
