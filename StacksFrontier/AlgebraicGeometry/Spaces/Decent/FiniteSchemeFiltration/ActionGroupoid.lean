module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration.FiberPower
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ResidueDegreeBound

/-!
# The permutation action on the distinct-tuple locus of a fibre power

The action of the symmetric group on the locus of pairwise distinct coordinates of a fibre
power of an étale chart, its étaleness and its freeness on the big fppf site, the action
relation as a finite locally free étale equivalence relation, and facts about fppf
coverings used for descent along it.

This is the second part of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v u₁ v₁

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_actionGroupoid
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_actionGroupoid
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Coordinate permutations restricted to the distinct-tuple locus. -/
noncomputable def distinctFiberPowerPermute
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    (distinctFiberPowerLocus B S hS f hf ho hc n).toScheme ⟶
      (distinctFiberPowerLocus B S hS f hf ho hc n).toScheme :=
  Scheme.Hom.resLE
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (fiberPowerPermute f hf n σ))
    _ _ (mapsTo_distinctFiberPowerLocus B S hS f hf ho hc n σ)

private theorem distinctFiberPowerPermute_ι
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    distinctFiberPowerPermute B S hS f hf ho hc n σ ≫
        (distinctFiberPowerLocus B S hS f hf ho hc n).ι =
      (distinctFiberPowerLocus B S hS f hf ho hc n).ι ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (fiberPowerPermute f hf n σ) :=
  Scheme.Hom.resLE_comp_ι _ _

theorem distinctFiberPowerPermute_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ) (σ τ : Equiv.Perm (Fin (n + 1))) :
    distinctFiberPowerPermute B S hS f hf ho hc n σ ≫
        distinctFiberPowerPermute B S hS f hf ho hc n τ =
      distinctFiberPowerPermute B S hS f hf ho hc n (τ.trans σ) := by
  apply (cancel_mono (distinctFiberPowerLocus B S hS f hf ho hc n).ι).mp
  rw [Category.assoc, distinctFiberPowerPermute_ι, ← Category.assoc,
    distinctFiberPowerPermute_ι, Category.assoc, ← CategoryTheory.Functor.map_comp,
    fiberPowerPermute_comp, distinctFiberPowerPermute_ι]

theorem distinctFiberPowerPermute_refl
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f)) (n : ℕ) :
    distinctFiberPowerPermute B S hS f hf ho hc n (Equiv.refl _) = 𝟙 _ := by
  have he : fiberPowerPermute f hf n (Equiv.refl _) = 𝟙 _ := by
    apply fiberPower_hom_ext f hf n
    intro i
    simp only [fiberPowerPermute_projection, Equiv.refl_apply, Category.id_comp]
  apply (cancel_mono (distinctFiberPowerLocus B S hS f hf ho hc n).ι).mp
  rw [distinctFiberPowerPermute_ι, he, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp]

private noncomputable def distinctFiberPowerPermutationIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    (distinctFiberPowerLocus B S hS f hf ho hc n).toScheme ≅
      (distinctFiberPowerLocus B S hS f hf ho hc n).toScheme where
  hom := distinctFiberPowerPermute B S hS f hf ho hc n σ
  inv := distinctFiberPowerPermute B S hS f hf ho hc n σ.symm
  hom_inv_id := by
    rw [distinctFiberPowerPermute_comp, Equiv.symm_trans_self, distinctFiberPowerPermute_refl]
  inv_hom_id := by
    rw [distinctFiberPowerPermute_comp, Equiv.self_trans_symm, distinctFiberPowerPermute_refl]

private theorem coordinateDiagonal_lift_of_eq
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U T : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (hd : yoneda.relativelyRepresentable (pullback.diagonal f))
    (n : ℕ) (g : T ⟶ (fiberPower f hf n).1) (i j : Fin (n + 1))
    (hij : g ≫ fiberPowerProjection f hf n i = g ≫ fiberPowerProjection f hf n j) :
    ∃ l : T ⟶ hd.pullback (fiberPowerPair f hf n i j),
      l ≫ hd.snd (fiberPowerPair f hf n i j) = g := by
  have hw : yoneda.map (g ≫ fiberPowerProjection f hf n i) ≫ pullback.diagonal f =
      yoneda.map g ≫ fiberPowerPair f hf n i j := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id,
        fiberPowerPair, pullback.lift_fst, Functor.map_comp]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id,
        fiberPowerPair, pullback.lift_snd, ← Functor.map_comp]
      exact congrArg (fun k ↦ yoneda.map k) hij
  exact ⟨hd.lift _ g hw, hd.lift_snd _ _ _⟩

theorem injective_coordinates_of_mapsTo_distinctFiberPowerLocus
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U T : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ) (g : T ⟶ (fiberPower f hf n).1)
    (hT : Nonempty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T))
    (hg : Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ⊆
      distinctFiberPowerLocus B S hS f hf ho hc n) :
    Function.Injective (fun i => g ≫ fiberPowerProjection f hf n i) := by
  intro i j hij
  by_contra hne
  obtain ⟨x⟩ := hT
  obtain ⟨l, hl⟩ := coordinateDiagonal_lift_of_eq f hf ho.rep n g i j hij
  apply hg ⟨x, rfl⟩
  refine Set.mem_iUnion.mpr ⟨⟨(i, j), hne⟩, ?_⟩
  refine ⟨((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map l) x, ?_⟩
  have h := congrArg ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map) hl
  simpa only [Functor.map_comp, Scheme.Hom.comp_apply] using
    congrArg (fun k ↦ k x) h

private theorem injective_permutations_of_mapsTo_distinctFiberPowerLocus
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U T : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ) (g : T ⟶ (fiberPower f hf n).1)
    (hT : Nonempty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T))
    (hg : Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ⊆
      distinctFiberPowerLocus B S hS f hf ho hc n) :
    Function.Injective (fun σ => g ≫ fiberPowerPermute f hf n σ) :=
  fiberPowerPermute_injective f hf n g
    (injective_coordinates_of_mapsTo_distinctFiberPowerLocus B S hS f hf ho hc n g hT hg)

noncomputable def distinctFiberPowerAction
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f)) (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) →*
      End (distinctFiberPowerLocus B S hS f hf ho hc n).toScheme where
  toFun σ := .of (distinctFiberPowerPermute B S hS f hf ho hc n σ.symm)
  map_one' := End.ext (distinctFiberPowerPermute_refl B S hS f hf ho hc n)
  map_mul' σ τ := by
    ext1
    rw [End.mul_asHom, distinctFiberPowerPermute_comp, Equiv.Perm.mul_def,
      Equiv.symm_trans]

/-- A set-theoretic mapping condition between two opens, read as an inequality of opens. -/
theorem le_preimage_of_mapsTo {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (L : Y.Opens) (L' : Z.Opens) (hm : Set.MapsTo g L L') : L ≤ g ⁻¹ᵁ L' :=
  fun _ hx ↦ hm hx

/-- The restriction of a morphism `m : T ⟶ T'` of site objects to a morphism of open
subobjects, given that `m` carries the open `L` of `T` into the open `L'` of `T'`. Taking
`T' = T` and `L' = L` gives the restriction of an endomorphism to an invariant open. -/
def openSubschemeMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS}
    (L : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T).Opens)
    (L' : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T').Opens)
    (m : T ⟶ T')
    (hm : Set.MapsTo ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m) L L') :
    opensSiteObject B S hS T L ⟶ opensSiteObject B S hS T' L' :=
  Over.homMk ⟨Scheme.Hom.resLE
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m) L' L
    (le_preimage_of_mapsTo _ L L' hm)⟩ (by
      apply ObjectProperty.hom_ext
      change Scheme.Hom.resLE ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m) L' L
            (le_preimage_of_mapsTo _ L L' hm) ≫
            (opensSiteObject B S hS T' L').hom.hom = (opensSiteObject B S hS T L).hom.hom
      rw [hom_opensSiteObject, hom_opensSiteObject,
        ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
      exact congrArg (fun a ↦ L.ι ≫ a) (congrArg (fun a ↦ a.hom) m.w))

/-- The restriction of a morphism to open subobjects commutes with the inclusions of those
subobjects into the ambient site objects. -/
theorem openSubschemeMap_inclusion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS}
    (L : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T).Opens)
    (L' : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T').Opens)
    (m : T ⟶ T')
    (hm : Set.MapsTo ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m) L L') :
    openSubschemeMap B S hS L L' m hm ≫ opensSiteObjectInclusion B S hS T' L' =
      opensSiteObjectInclusion B S hS T L ≫ m := by
  apply (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective
  simp only [Functor.map_comp, map_opensSiteObjectInclusion]
  exact Scheme.Hom.resLE_comp_ι _ _

/-- Forgetting the newest coordinate of a fibre power is compatible with the maps of the
distinct loci to the ambient presheaf. -/
theorem openSubschemeMap_snd_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f)) (n : ℕ) :
    yoneda.map (openSubschemeMap B S hS
        (distinctFiberPowerLocus B S hS f hf ho hc (n + 1))
        (distinctFiberPowerLocus B S hS f hf ho hc n)
        (hf.snd (fiberPower f hf n).2)
        (mapsTo_distinctFiberPowerLocus_snd B S hS f hf ho hc n)) ≫
      (yoneda.map (opensSiteObjectInclusion B S hS (fiberPower f hf n).1
          (distinctFiberPowerLocus B S hS f hf ho hc n)) ≫ (fiberPower f hf n).2) =
      yoneda.map (opensSiteObjectInclusion B S hS (fiberPower f hf (n + 1)).1
          (distinctFiberPowerLocus B S hS f hf ho hc (n + 1))) ≫
        (fiberPower f hf (n + 1)).2 := by
  have hc' := openSubschemeMap_inclusion B S hS
    (distinctFiberPowerLocus B S hS f hf ho hc (n + 1))
    (distinctFiberPowerLocus B S hS f hf ho hc n)
    (hf.snd (fiberPower f hf n).2)
    (mapsTo_distinctFiberPowerLocus_snd B S hS f hf ho hc n)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k ↦ k ≫ (fiberPower f hf n).2)
    (((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map hc')).trans
      (yoneda.map_comp _ _))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun k ↦ yoneda.map (opensSiteObjectInclusion B S hS
      (fiberPower f hf (n + 1)).1
      (distinctFiberPowerLocus B S hS f hf ho hc (n + 1))) ≫ k)
    (hf.w (fiberPower f hf n).2).symm

theorem distinctFiberPowerPermute_comp_structureMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    let W := distinctFiberPowerLocus B S hS f hf ho hc n
    let i := opensSiteObjectInclusion B S hS (fiberPower f hf n).1 W
    let m := openSubschemeMap B S hS W W
      (fiberPowerPermute f hf n σ) (mapsTo_distinctFiberPowerLocus B S hS f hf ho hc n σ)
    yoneda.map m ≫ yoneda.map i ≫ (fiberPower f hf n).2 =
      yoneda.map i ≫ (fiberPower f hf n).2 := by
  dsimp only
  rw [← Category.assoc, ← Functor.map_comp, openSubschemeMap_inclusion,
    Functor.map_comp, Category.assoc, fiberPowerPermute_comp_base]

private theorem property_fiberPower
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (P : MorphismProperty C) [P.IsStableUnderComposition]
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (hP : P.presheaf f) (n : ℕ) : P.presheaf (fiberPower f hf n).2 := by
  let := P.relative_isStableUnderBaseChange (F := yoneda)
  induction n with
  | zero => exact hP
  | succ n ih =>
      show P.presheaf (hf.fst (fiberPower f hf n).2 ≫ f)
      rw [hf.w]
      exact P.presheaf.comp_mem _ _
        (P.presheaf.of_isPullback (hf.isPullback (fiberPower f hf n).2) hP) ih

theorem etale_fiberPower
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f) (n : ℕ) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (fiberPower f hf n).2 := by
  exact property_fiberPower (MorphismProperty.inverseImage (@Etale.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) f hf he n

private theorem presheaf_inverseImage_yoneda_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (f : U ⟶ V)
    (hf : P ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f)) :
    (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map f) := by
  let q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : (P.inverseImage q).IsStableUnderBaseChange := ⟨fun sq h ↦
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P) (sq.map q) h⟩
  exact MorphismProperty.relative_map (F := yoneda) hf

theorem etale_distinctFiberPowerLocus
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f) (n : ℕ) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (opensSiteObjectInclusion B S hS (fiberPower f hf n).1
        (distinctFiberPowerLocus B S hS f hf ho hc n)) ≫ (fiberPower f hf n).2) := by
  have hi := presheaf_inverseImage_yoneda_map B S hS (@Etale.{u})
    (opensSiteObjectInclusion B S hS (fiberPower f hf n).1
      (distinctFiberPowerLocus B S hS f hf ho hc n)) (by
      rw [map_opensSiteObjectInclusion]
      exact inferInstanceAs (Etale (distinctFiberPowerLocus B S hS f hf ho hc n).ι))
  exact (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf.comp_mem _ _ hi
    (etale_fiberPower B S hS f hf he n)

theorem presheaf_yoneda_map_of_scheme_property
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (f : U ⟶ V)
    (hf : P ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f)) :
    (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map f) :=
  presheaf_inverseImage_yoneda_map B S hS P f hf

theorem isEtale_of_representablyEtale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f) :
    AlgebraicGeometry.Space.IsEtale B S hS f := by
  intro U φ hφ
  exact (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf.comp_mem φ f hφ hf

noncomputable def distinctFiberPowerSiteAction
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f)) (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) →* End (opensSiteObject B S hS
      (fiberPower f hf n).1 (distinctFiberPowerLocus B S hS f hf ho hc n)) where
  toFun σ := .of (openSubschemeMap B S hS
    (distinctFiberPowerLocus B S hS f hf ho hc n)
    (distinctFiberPowerLocus B S hS f hf ho hc n) (fiberPowerPermute f hf n σ.symm)
    (mapsTo_distinctFiberPowerLocus B S hS f hf ho hc n σ.symm))
  map_one' := End.ext <| (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective
    (distinctFiberPowerPermute_refl B S hS f hf ho hc n)
  map_mul' σ τ := End.ext <| (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective
    (congrArg End.asHom ((distinctFiberPowerAction B S hS f hf ho hc n).map_mul σ τ))

theorem injective_distinctFiberPowerSiteAction
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U T : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f)) (n : ℕ)
    (g : T ⟶ opensSiteObject B S hS (fiberPower f hf n).1
      (distinctFiberPowerLocus B S hS f hf ho hc n))
    (hT : Nonempty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)) :
    Function.Injective
      (fun σ => g ≫ (distinctFiberPowerSiteAction B S hS f hf ho hc n σ).asHom) := by
  let i := opensSiteObjectInclusion B S hS (fiberPower f hf n).1
    (distinctFiberPowerLocus B S hS f hf ho hc n)
  have hg : Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (g ≫ i)) ⊆
      distinctFiberPowerLocus B S hS f hf ho hc n :=
    range_map_comp_opensSiteObjectInclusion B S hS _ g
  intro σ τ h
  suffices hs : σ.symm = τ.symm by
    simpa only [Equiv.symm_symm] using congrArg Equiv.symm hs
  apply injective_permutations_of_mapsTo_distinctFiberPowerLocus B S hS f hf ho hc n
    (g ≫ i) hT hg
  have hh := congrArg (fun k ↦ k ≫ i) h
  dsimp only [distinctFiberPowerSiteAction, MonoidHom.coe_mk, OneHom.coe_mk, i] at hh
  simpa only [Category.assoc, openSubschemeMap_inclusion] using hh

theorem residueFieldFaithful_of_siteFree
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (G : Type v) [Group G]
    (a : G →* Aut U)
    (hfree : ∀ (T : AlgebraicGeometry.BigFppfOver B S hS) (g : T ⟶ U),
      Nonempty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) →
        Function.Injective (fun σ => g ≫ (a σ).asIso.hom)) :
    AlgebraicGeometry.Space.ActsNontriviallyOnFixedResidueFields
      ((Over.post B.inclusion).obj U) G
      (((Over.post B.inclusion).mapAut U).comp a) := by
  let q : AlgebraicGeometry.BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  intro σ x hx hσ hres
  let Y := (q.obj U).left
  have hk : B.Contains (Spec (Y.residueField x)) :=
    Scheme.size_lt_of_mono_quasiCompact (Y.fromSpecResidueField x) U.left.property
  let K := B.obj hk
  let z : K ⟶ U.left :=
    B.inclusion.preimage (X := K) (Y := U.left) (Y.fromSpecResidueField x)
  let T : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (z ≫ U.hom)
  let g : T ⟶ U := Over.homMk z (by rfl)
  have hfixed : Y.fromSpecResidueField x ≫
      ((q.mapAut U).comp a σ).asIso.hom.left = Y.fromSpecResidueField x := by
    have hmap := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
      (f := ((q.mapAut U).comp a σ).asIso.hom.left) x
    rw [hres] at hmap
    exact hmap.symm.trans (Y.residueFieldCongr_fromSpecResidueField hx)
  have hsite : g ≫ (a σ).asIso.hom = g := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    show B.inclusion.map (z ≫ (a σ).asIso.hom.left) = B.inclusion.map z
    rw [Functor.map_comp]
    have hz : B.inclusion.map z = Y.fromSpecResidueField x := by
      dsimp only [z]
      exact B.inclusion.map_preimage _
    rw [hz]
    exact hfixed
  have hT : Nonempty (q.obj T).left := by
    show Nonempty (Spec (Y.residueField x))
    infer_instance
  apply hσ
  apply hfree T g hT
  simp only [map_one]
  show g ≫ (a σ).asIso.hom = g ≫ 𝟙 U
  simpa only [Category.comp_id] using hsite

private theorem actionRelationSource_desc
    {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G] [Small.{u} G] :
    (actionRelationUnderlyingIso U G).inv ≫
        (AlgebraicGeometry.Space.actionRelationSource U G).left =
      Sigma.desc (fun _ : G ↦ 𝟙 U.left) := by
  apply Sigma.hom_ext
  intro g
  rw [← Category.assoc, actionRelationUnderlyingIso_inv_ι]
  show (Sigma.ι (fun _ : G ↦ U) g ≫
    AlgebraicGeometry.Space.actionRelationSource U G).left = _
  simp [AlgebraicGeometry.Space.actionRelationSource]

private theorem actionRelationTarget_desc
    {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G] [Small.{u} G]
    (a : G →* Aut U) :
    (actionRelationUnderlyingIso U G).inv ≫
        (AlgebraicGeometry.Space.actionRelationTarget U G a).left =
      Sigma.desc (fun g : G ↦ (a g).asIso.hom.left) := by
  apply Sigma.hom_ext
  intro g
  rw [← Category.assoc, actionRelationUnderlyingIso_inv_ι]
  show (Sigma.ι (fun _ : G ↦ U) g ≫
    AlgebraicGeometry.Space.actionRelationTarget U G a).left = _
  simp [AlgebraicGeometry.Space.actionRelationTarget]

/-- A morphism out of the coproduct of copies of `U.left` that is an isomorphism on each copy
is finite locally free. -/
private theorem isFiniteLocallyFree_of_inv_comp_eq_sigmaDesc
    {S : Scheme.{u}} (U : Over S) (G : Type v) [Group G] [Small.{u} G] [Finite G]
    {Y : Scheme.{u}} (s : (AlgebraicGeometry.Space.actionRelationScheme U G).left ⟶ Y)
    (φ : G → (U.left ⟶ Y)) [∀ g, IsIso (φ g)]
    (hs : (actionRelationUnderlyingIso U G).inv ≫ s = Sigma.desc φ) :
    Stacks.Morphisms.IsFiniteLocallyFree s := by
  let e := actionRelationUnderlyingIso U G
  have hcomp : e.hom ≫ (e.inv ≫ s) = s := by simp
  have : _root_.AlgebraicGeometry.IsFinite (e.inv ≫ s) := by rw [hs]; infer_instance
  have : Flat (e.inv ≫ s) := by rw [hs]; infer_instance
  have : LocallyOfFinitePresentation (e.inv ≫ s) := by
    let : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    rw [hs]
    exact IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  apply (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
  constructor
  · show _root_.AlgebraicGeometry.IsFinite s
    rw [← hcomp]
    infer_instance
  constructor
  · show Flat s
    rw [← hcomp]
    infer_instance
  · show LocallyOfFinitePresentation s
    rw [← hcomp]
    infer_instance

theorem actionRelationSource_isFiniteLocallyFree
    {S : Scheme.{u}} (U : Over S) (G : Type v)
    [Group G] [Small.{u} G] [Finite G] :
    Stacks.Morphisms.IsFiniteLocallyFree
      (AlgebraicGeometry.Space.actionRelationSource U G).left :=
  isFiniteLocallyFree_of_inv_comp_eq_sigmaDesc U G _ (fun _ : G ↦ 𝟙 U.left)
    (actionRelationSource_desc U G)

theorem actionRelationScheme_mem_site
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (G : Type v) [Group G] [Small.{u} G] [Finite G] :
    B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj U) G).left := by
  let O : Over S := (Over.post B.inclusion).obj U
  let s := (AlgebraicGeometry.Space.actionRelationSource O G).left
  have hfinite : _root_.AlgebraicGeometry.IsFinite s :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation s).mp
      (actionRelationSource_isFiniteLocallyFree O G) |>.1
  let : _root_.AlgebraicGeometry.IsFinite s := hfinite
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact s U.left.property

theorem actionRelationTarget_isFiniteLocallyFree
    {S : Scheme.{u}} (U : Over S) (G : Type v)
    [Group G] [Small.{u} G] [Finite G]
    (a : G →* Aut U) :
    Stacks.Morphisms.IsFiniteLocallyFree
      (AlgebraicGeometry.Space.actionRelationTarget U G a).left :=
  let (g : G) : IsIso (a g).asIso.hom.left := ((Over.forget S).mapIso (a g).asIso).isIso_hom
  isFiniteLocallyFree_of_inv_comp_eq_sigmaDesc U G _ (fun g : G ↦ (a g).asIso.hom.left)
    (actionRelationTarget_desc U G a)

/-- A property of the source and target maps holds for a groupoid scheme extending a
pre-relation exactly when it holds for the pre-relation. -/
private theorem source_target_iff_of_extendsRelation
    {S : Scheme.{u}} {R U : Over S}
    (j : Stacks.Groupoids.PreRelation R U) (H : Stacks.Groupoids.GroupoidScheme S)
    (h : AlgebraicGeometry.ExtendsRelation j H)
    (Q : ∀ {R U : Over S}, (R ⟶ U) → (R ⟶ U) → Prop) :
    Q H.source H.target ↔ Q j.source j.target := by
  rcases h with ⟨ho, ha, hs', ht'⟩
  rcases H with ⟨objects, arrows, source, target, comp, identity, inverse,
    source_identity, target_identity, source_inverse, target_inverse,
    source_comp, target_comp, left_identity, right_identity, left_inverse,
    right_inverse, assoc⟩
  dsimp only at ho ha
  subst objects
  subst arrows
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hs' ht'
  show Q source target ↔ _
  rw [hs', ht']

theorem finiteLocallyFree_of_extendsRelation
    {S : Scheme.{u}} {R U : Over S}
    (j : Stacks.Groupoids.PreRelation R U) (H : Stacks.Groupoids.GroupoidScheme S)
    (h : AlgebraicGeometry.ExtendsRelation j H)
    (hs : Stacks.Morphisms.IsFiniteLocallyFree j.source.left)
    (ht : Stacks.Morphisms.IsFiniteLocallyFree j.target.left) :
    Stacks.Morphisms.IsFiniteLocallyFree H.source.left ∧
      Stacks.Morphisms.IsFiniteLocallyFree H.target.left :=
  (source_target_iff_of_extendsRelation j H h fun s t ↦
    Stacks.Morphisms.IsFiniteLocallyFree s.left ∧
      Stacks.Morphisms.IsFiniteLocallyFree t.left).mpr ⟨hs, ht⟩

theorem isEquivalenceRelation_of_extendsRelation
    {S : Scheme.{u}} {R U : Over S}
    (j : Stacks.Groupoids.PreRelation R U) (H : Stacks.Groupoids.GroupoidScheme S)
    (h : AlgebraicGeometry.ExtendsRelation j H)
    [IsEquivalenceRelation j.target j.source] :
    IsEquivalenceRelation H.target H.source :=
  (source_target_iff_of_extendsRelation j H h fun s t ↦ IsEquivalenceRelation t s).mpr
    inferInstance

theorem kernelPair_of_extendsRelation
    {S : Scheme.{u}} {R U : Over S}
    (j : Stacks.Groupoids.PreRelation R U) (H : Stacks.Groupoids.GroupoidScheme S)
    (h : AlgebraicGeometry.ExtendsRelation j H) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) :
    IsPullback j.target j.source
      (eqToHom h.objects_eq.symm ≫ q) (eqToHom h.objects_eq.symm ≫ q) := by
  rcases h with ⟨ho, ha, hs', ht'⟩
  rcases H with ⟨objects, arrows, source, target, comp, identity, inverse,
    source_identity, target_identity, source_inverse, target_inverse,
    source_comp, target_comp, left_identity, right_identity, left_inverse,
    right_inverse, assoc⟩
  dsimp only at ho ha
  subst objects
  subst arrows
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hs' ht' ⊢
  change IsPullback target source q q at hq
  rwa [hs', ht'] at hq

theorem etale_target_of_extendsRelation
    {S : Scheme.{u}} {R U : Over S}
    (j : Stacks.Groupoids.PreRelation R U) (H : Stacks.Groupoids.GroupoidScheme S)
    (h : AlgebraicGeometry.ExtendsRelation j H)
    [Stacks.Groupoids.IsEtaleEquivalenceRelation j] : Etale H.target.left :=
  (source_target_iff_of_extendsRelation j H h fun _ t ↦ Etale t.left).mpr inferInstance

theorem etale_quotientMap_of_etale_target
    {S : Scheme.{u}} {G : Stacks.Groupoids.GroupoidScheme S}
    (Q : Stacks.Groupoids.FiniteFlatQuotient G) (he : Etale G.target.left) :
    Etale Q.quotientMap.left := by
  have hflf :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      Q.quotientMap.left).mp Q.finiteLocallyFree
  let : _root_.AlgebraicGeometry.IsFinite Q.quotientMap.left := hflf.1
  let : Flat Q.quotientMap.left := hflf.2.1
  have hpb : IsPullback G.target.left G.source.left
      Q.quotientMap.left Q.quotientMap.left :=
    Q.kernelPair.map (Over.forget S)
  exact MorphismProperty.of_isPullback_of_descendsAlong hpb
    (show (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u} :
        MorphismProperty Scheme.{u}) Q.quotientMap.left from
      ⟨⟨Q.surjective, inferInstance⟩, inferInstance⟩) he

theorem exists_openSubspace_etaleImage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    (f : yoneda.obj V ⟶ X) (hf : AlgebraicGeometry.Space.IsEtale B S hS f) :
    ∃ U : Subfunctor X, AlgebraicGeometry.Space.IsOpenSubspace B S hS U ∧
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) =
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj V) f) := by
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
    AlgebraicGeometry.Space.pointTopology B S hS X
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS (yoneda.obj V)) :=
    AlgebraicGeometry.Space.pointTopology B S hS (yoneda.obj V)
  let I := AlgebraicGeometry.Space.openSubspacesOrderIso B S hS X hX
  let O : TopologicalSpace.Opens (AlgebraicGeometry.Space.points B S hS X) :=
    ⟨Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj V) f),
      (AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isEtale B S hS f
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) hX hf).isOpen_range⟩
  let U := I.symm O
  refine ⟨U.1, U.2, ?_⟩
  have h := AlgebraicGeometry.Space.openSubspacesOrderIso_apply B S hS X hX U
  change (I U).1 = Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.1.toFunctor U.1.ι) at h
  rw [show I U = O by exact I.apply_symm_apply O] at h
  exact h.symm

private theorem generate_mem_bigFppfTopology
    (B : AlgebraicGeometry.BigFppfSite.{u}) {T : B.Schemes}
    (E : PreZeroHypercover.{u + 1} T)
    (hE : E.presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion T) :
    Sieve.generate E.presieve₀ ∈ B.topology T := by
  obtain ⟨⟨T', E'⟩, hE', h, hc⟩ := B.fppf_has_representative ⟨T, E⟩ hE
  dsimp at h
  subst T'
  have heq : E.presieve₀ = E'.presieve₀ :=
    PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hc
  rw [heq]
  exact Precoverage.generate_mem_toGrothendieck ⟨E', rfl, hE'⟩

theorem ofArrows_mem_bigFppfOverTopology
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : AlgebraicGeometry.BigFppfOver B S hS} {I : Type u}
    (Y : I → AlgebraicGeometry.BigFppfOver B S hS) (f : ∀ i, Y i ⟶ T)
    (hcov : ∀ t : B.inclusion.obj T.left,
      ∃ i x, (B.inclusion.map (f i).left) x = t)
    (hflat : ∀ i, Flat (B.inclusion.map (f i).left))
    (hfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (f i).left)) :
    Sieve.ofArrows Y f ∈ AlgebraicGeometry.BigFppfOver.topology B S hS T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  let E : PreZeroHypercover.{u + 1} T.left :=
    ⟨ULift.{u + 1} I, fun i ↦ (Y i.down).left, fun i ↦ (f i.down).left⟩
  have heq : E.presieve₀ =
      Presieve.ofArrows (fun i ↦ (Y i).left) (fun i ↦ (f i).left) := by
    funext Z g
    exact propext ⟨fun ⟨i⟩ ↦ ⟨i.down⟩, fun ⟨i⟩ ↦ ⟨ULift.up i⟩⟩
  rw [Sieve.ofArrows, ← heq]
  apply generate_mem_bigFppfTopology B E
  rw [Precoverage.mem_comap_iff, heq, Presieve.map_ofArrows]
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨hcov, fun i ↦ ⟨hflat i, hfp i⟩⟩

private theorem singleton_mem_bigFppfOverTopology
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : AlgebraicGeometry.BigFppfOver B S hS} (q : W ⟶ V)
    (hsurj : Surjective ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q))
    (hflat : Flat ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q))
    (hfp : LocallyOfFinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)) :
    Sieve.generate (Presieve.singleton q) ∈
      AlgebraicGeometry.BigFppfOver.topology B S hS V := by
  rw [← Presieve.ofArrows_pUnit.{u}]
  exact ofArrows_mem_bigFppfOverTopology B S hS (fun _ : PUnit.{u + 1} ↦ W)
    (fun _ ↦ q)
    (fun t ↦ by obtain ⟨x, hx⟩ := hsurj.surj t; exact ⟨PUnit.unit, x, hx⟩)
    (fun _ ↦ hflat) (fun _ ↦ hfp)

/-- A section over the source of a surjective flat morphism of finite
presentation whose two pullbacks agree descends uniquely to the target. -/
theorem exists_unique_descent_along_fppf_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) F)
    {W V : AlgebraicGeometry.BigFppfOver B S hS} (q : W ⟶ V)
    (hsurj : Surjective ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q))
    (hflat : Flat ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q))
    (hfp : LocallyOfFinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q))
    (x : F.obj (Opposite.op W))
    (hx : ∀ {Z : AlgebraicGeometry.BigFppfOver B S hS} (p₁ p₂ : Z ⟶ W),
      p₁ ≫ q = p₂ ≫ q → F.map p₁.op x = F.map p₂.op x) :
    ∃! y : F.obj (Opposite.op V), F.map q.op y = x := by
  have hc := singleton_mem_bigFppfOverTopology B S hS q hsurj hflat hfp
  have hs := (Presieve.isSheafFor_iff_generate (P := F) (Presieve.singleton q)).mpr
    (hF.isSheafFor _ hc)
  exact Presieve.isSheafFor_singleton.mp hs x hx

end AlgebraicGeometry.Space

end
