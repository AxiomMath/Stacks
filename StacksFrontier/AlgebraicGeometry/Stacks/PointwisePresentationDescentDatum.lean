module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescentEssSurj

/-!
# Nested inverse images along morphisms of algebraic spaces

For morphisms of algebraic spaces `k₁ : X ⟶ Y`, `t₁ : Y ⟶ Z`, `k₂ : X ⟶ Y'`, `t₂ : Y' ⟶ Z` with
`k₁ ≫ t₁ = k₂ ≫ t₂` and a module `M` on the fppf site of `𝒮_Z`, the two nested inverse images
`k₁^*t₁^*M` and `k₂^*t₂^*M` on `𝒮_X` are identified by restriction of sections along the
canonical 2-morphism between the two composite 1-morphisms.

## Main definitions

* `AlgebraicGeometry.Stack.spaceNestedTransport`: the transport `k₁^*t₁^*M ⟶ k₂^*t₂^*M`.

## Main results

* `AlgebraicGeometry.Stack.eq_of_val_app_chart`: morphisms of quasi-coherent modules on `𝒮_Y`
  are determined by their components at the étale charts of `Y`, the faithfulness half of
  Stacks 0GQD.
* `AlgebraicGeometry.Stack.restrictionMap_eq_spaceTwoMorphism`: the restriction of a descent
  morphism along `k` is a transport as soon as its transition reindexes to a transport along `k`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

section Spaces

variable {X Y Z : AlgebraicSpaces C S hS}

/-- The 2-morphism of 1-morphisms `𝒮_X ⥤ 𝒮_Z` attached to an equality `k₁ ≫ t₁ = k₂ ≫ t₂`. -/
abbrev spaceCompTwoMorphism {Y' : AlgebraicSpaces C S hS} {k₁ : X ⟶ Y} {t₁ : Y ⟶ Z}
    {k₂ : X ⟶ Y'} {t₂ : Y' ⟶ Z} (h : k₁ ≫ t₁ = k₂ ≫ t₂) :
    spaceFunctor k₂ ⋙ spaceFunctor t₂ ⟶ spaceFunctor k₁ ⋙ spaceFunctor t₁ :=
  eqToHom (congrArg spaceFunctor h).symm

/-- For an equality of functors `F = G`, the component at `W` of `eqToHom` lies over the
identity of `q.obj (F.obj W)`. -/
theorem isHomLift_eqToHom_app_target {𝒳 𝒴 𝒮 : Type*} [Category 𝒳] [Category 𝒴] [Category 𝒮]
    (q : 𝒴 ⥤ 𝒮) {F G : 𝒳 ⥤ 𝒴} (e : F = G) (W : 𝒳) :
    q.IsHomLift (𝟙 (q.obj (F.obj W))) ((eqToHom e).app W) := by
  subst e
  exact IsHomLift.id rfl

/-- For an equality of functors `F = G` with `F ⋙ q = p`, the component at `W` of `eqToHom` lies
over the identity of `p.obj W`. -/
theorem isHomLift_eqToHom_app_source {𝒳 𝒴 𝒮 : Type*} [Category 𝒳] [Category 𝒴] [Category 𝒮]
    (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) {F G : 𝒳 ⥤ 𝒴} (hF : F ⋙ q = p) (e : F = G) (W : 𝒳) :
    q.IsHomLift (𝟙 (p.obj W)) ((eqToHom e).app W) := by
  subst e hF
  exact IsHomLift.id rfl

/-- The component at `W` of `spaceCompTwoMorphism h` lies over the identity of
`(spaceProj Z).obj ((spaceFunctor k₂ ⋙ spaceFunctor t₂).obj W)`. -/
theorem isHomLift_spaceCompTwoMorphism {Y' : AlgebraicSpaces C S hS} {k₁ : X ⟶ Y} {t₁ : Y ⟶ Z}
    {k₂ : X ⟶ Y'} {t₂ : Y' ⟶ Z} (h : k₁ ≫ t₁ = k₂ ≫ t₂) (W : spaceCat X) :
    (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj ((spaceFunctor k₂ ⋙ spaceFunctor t₂).obj W)))
      ((spaceCompTwoMorphism h).app W) :=
  isHomLift_eqToHom_app_target _ _ W

/-- The composite `spaceFunctor k ⋙ spaceFunctor t` commutes with the projections to the base. -/
theorem spaceFunctor_comp_comp_spaceProj (k : X ⟶ Y) (t : Y ⟶ Z) :
    (spaceFunctor k ⋙ spaceFunctor t) ⋙ spaceProj Z = spaceProj X := by
  rw [Functor.assoc, spaceFunctor_comp_spaceProj, spaceFunctor_comp_spaceProj]

/-- The component at `W` of `spaceCompTwoMorphism h` lies over the identity of
`(spaceProj X).obj W`. -/
theorem isHomLift_spaceCompTwoMorphism_source {Y' : AlgebraicSpaces C S hS} {k₁ : X ⟶ Y}
    {t₁ : Y ⟶ Z} {k₂ : X ⟶ Y'} {t₂ : Y' ⟶ Z} (h : k₁ ≫ t₁ = k₂ ≫ t₂) (W : spaceCat X) :
    (spaceProj Z).IsHomLift (𝟙 ((spaceProj X).obj W)) ((spaceCompTwoMorphism h).app W) :=
  isHomLift_eqToHom_app_source _ _ (spaceFunctor_comp_comp_spaceProj k₂ t₂) _ W

/-- The structure sheaf of rings of `𝒮_X`, in the spelling of
`AlgebraicGeometry.Stack.modulePullback`. -/
abbrev spaceStackRing (X : AlgebraicSpaces C S hS) :=
  ringStructureSheafCore C S hS (spaceProj X) (isFiberedInGroupoids_spaceProj X) C.topology
    (topology_le_self C)

/-- The functor `spaceFunctor k : 𝒮_X ⥤ 𝒮_Y` is continuous for the fppf topologies. -/
theorem isContinuous_spaceFunctor (k : X ⟶ Y) :
    (spaceFunctor k).IsContinuous (associatedTopology C S hS (spaceProj X) C.topology)
      (associatedTopology C S hS (spaceProj Y) C.topology) :=
  isContinuous_associatedTopology _ _ (isFiberedInGroupoids_spaceProj X)
    (isFiberedInGroupoids_spaceProj Y) (spaceFunctor k) (spaceFunctor_comp_spaceProj k)

/-- The composite `spaceFunctor k ⋙ spaceFunctor t : 𝒮_X ⥤ 𝒮_Z` is continuous for the fppf
topologies. -/
theorem isContinuous_spaceFunctor_comp (k : X ⟶ Y) (t : Y ⟶ Z) :
    (spaceFunctor k ⋙ spaceFunctor t).IsContinuous
      (associatedTopology C S hS (spaceProj X) C.topology)
      (associatedTopology C S hS (spaceProj Z) C.topology) :=
  isContinuous_associatedTopology _ _ (isFiberedInGroupoids_spaceProj X)
    (isFiberedInGroupoids_spaceProj Z) (spaceFunctor k ⋙ spaceFunctor t)
    (spaceFunctor_comp_comp_spaceProj k t)

/-- The scalar identification of `AlgebraicGeometry.Stack.modulePullback` along `k`. -/
abbrev spaceRingHom (k : X ⟶ Y) :
    haveI := isContinuous_spaceFunctor k
    spaceStackRing X ⟶ ((spaceFunctor k).sheafPushforwardContinuous RingCat.{u} _ _).obj
      (spaceStackRing Y) :=
  ⟨eqToHom (ringStructureSheafCore_obj_eq C S hS (spaceProj X) (spaceProj Y)
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y) (spaceFunctor k)
    (spaceFunctor_comp_spaceProj k) C.topology (topology_le_self C))⟩

/-- The scalar identification of `k^*(t^*M)`. -/
abbrev spaceNestedRingHom (k : X ⟶ Y) (t : Y ⟶ Z) :
    haveI := isContinuous_spaceFunctor_comp k t
    spaceStackRing X ⟶ ((spaceFunctor k ⋙ spaceFunctor t).sheafPushforwardContinuous
      RingCat.{u} _ _).obj (spaceStackRing Z) :=
  haveI := isContinuous_spaceFunctor k
  haveI := isContinuous_spaceFunctor t
  spaceRingHom k ≫ ((spaceFunctor k).sheafPushforwardContinuous RingCat.{u} _ _).map
    (spaceRingHom t)

/-- The scalar identifications of the two nested inverse images are compatible with the
2-morphism `spaceCompTwoMorphism h`. -/
theorem spaceNestedRingHom_comp_twoMorphism {Y' : AlgebraicSpaces C S hS} {k₁ : X ⟶ Y}
    {t₁ : Y ⟶ Z} {k₂ : X ⟶ Y'} {t₂ : Y' ⟶ Z} (h : k₁ ≫ t₁ = k₂ ≫ t₂) :
    haveI := isContinuous_spaceFunctor_comp k₁ t₁
    haveI := isContinuous_spaceFunctor_comp k₂ t₂
    spaceNestedRingHom k₁ t₁ ≫ (Functor.sheafPushforwardContinuousNatTrans
      (spaceCompTwoMorphism h) RingCat.{u} _ _).app (spaceStackRing Z) =
      spaceNestedRingHom k₂ t₂ := by
  have hw := whiskerRight_op_ringStructureSheafCore C S hS (spaceProj X) (spaceProj Z)
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Z)
    (spaceFunctor_comp_comp_spaceProj k₂ t₂) (spaceFunctor_comp_comp_spaceProj k₁ t₁)
    (spaceCompTwoMorphism h) (isHomLift_spaceCompTwoMorphism_source h) C.topology
    (topology_le_self C)
  apply Sheaf.hom_ext
  change (eqToHom (ringStructureSheafCore_obj_eq C S hS (spaceProj X) (spaceProj Y)
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y) (spaceFunctor k₁)
        (spaceFunctor_comp_spaceProj k₁) C.topology (topology_le_self C)) ≫
      Functor.whiskerLeft (spaceFunctor k₁).op
        (eqToHom (ringStructureSheafCore_obj_eq C S hS (spaceProj Y) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Y) (isFiberedInGroupoids_spaceProj Z) (spaceFunctor t₁)
          (spaceFunctor_comp_spaceProj t₁) C.topology (topology_le_self C)))) ≫
      (Functor.whiskerRight (NatTrans.op (spaceCompTwoMorphism h)) (spaceStackRing Z).obj :
        (spaceFunctor k₁).op ⋙ (spaceFunctor t₁).op ⋙ (spaceStackRing Z).obj ⟶
          (spaceFunctor k₂).op ⋙ (spaceFunctor t₂).op ⋙ (spaceStackRing Z).obj) =
    eqToHom (ringStructureSheafCore_obj_eq C S hS (spaceProj X) (spaceProj Y')
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y') (spaceFunctor k₂)
        (spaceFunctor_comp_spaceProj k₂) C.topology (topology_le_self C)) ≫
      Functor.whiskerLeft (spaceFunctor k₂).op
        (eqToHom (ringStructureSheafCore_obj_eq C S hS (spaceProj Y') (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Y') (isFiberedInGroupoids_spaceProj Z) (spaceFunctor t₂)
          (spaceFunctor_comp_spaceProj t₂) C.topology (topology_le_self C)))
  rw [hw]
  refine NatTrans.ext (funext fun x => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, eqToHom_trans]

/-- The inverse image `k^*`, in the spelling of `AlgebraicGeometry.Stack.modulePullback`. -/
abbrev stackPullback (k : X ⟶ Y) :
    SheafOfModules.{u} (spaceStackRing Y) ⥤ SheafOfModules.{u} (spaceStackRing X) :=
  modulePullback C S hS (spaceProj X) (spaceProj Y) (isFiberedInGroupoids_spaceProj X)
    (isFiberedInGroupoids_spaceProj Y) (spaceFunctor k) (spaceFunctor_comp_spaceProj k)
    C.topology (topology_le_self C)

/-- **The transport `k₁^*t₁^*M ⟶ k₂^*t₂^*M` attached to an equality `k₁ ≫ t₁ = k₂ ≫ t₂`**:
restriction of sections of `M` along the components of `spaceCompTwoMorphism`. -/
def spaceNestedTransport {Y' : AlgebraicSpaces C S hS} {k₁ : X ⟶ Y} {t₁ : Y ⟶ Z}
    {k₂ : X ⟶ Y'} {t₂ : Y' ⟶ Z} (h : k₁ ≫ t₁ = k₂ ≫ t₂)
    (M : SheafOfModules.{u} (spaceStackRing Z)) :
    (stackPullback k₁).obj ((stackPullback t₁).obj M) ⟶
      (stackPullback k₂).obj ((stackPullback t₂).obj M) :=
  haveI := isContinuous_spaceFunctor k₁
  haveI := isContinuous_spaceFunctor t₁
  haveI := isContinuous_spaceFunctor k₂
  haveI := isContinuous_spaceFunctor t₂
  haveI := isContinuous_spaceFunctor_comp k₁ t₁
  haveI := isContinuous_spaceFunctor_comp k₂ t₂
  (SheafOfModules.pushforwardComp (spaceRingHom k₁) (spaceRingHom t₁)).hom.app M ≫
    (SheafOfModules.pushforwardNatTrans (spaceNestedRingHom k₁ t₁) (spaceCompTwoMorphism h)).app M ≫
    (SheafOfModules.pushforwardCongr (spaceNestedRingHom_comp_twoMorphism h)).hom.app M ≫
    (SheafOfModules.pushforwardComp (spaceRingHom k₂) (spaceRingHom t₂)).inv.app M

/-- Morphisms of quasi-coherent modules on `𝒮_Y` with equal images under
`spaceQuasicoherentRestriction Y` are equal. -/
private theorem eq_of_restriction_map_eq {P₁ P₂ : FibredSite.quasicoherentModules.{u, u + 1, u, u}
      C S hS (spaceProj Y) (isFiberedInGroupoids_spaceProj Y)} {φ₁ φ₂ : P₁.obj ⟶ P₂.obj}
    (h : (spaceQuasicoherentRestriction Y).map (ObjectProperty.homMk φ₁ : P₁ ⟶ P₂) =
      (spaceQuasicoherentRestriction Y).map (ObjectProperty.homMk φ₂ : P₁ ⟶ P₂)) : φ₁ = φ₂ :=
  congrArg (fun ψ => ψ.hom) ((spaceQuasicoherentRestriction Y).map_injective h)

/-- **Morphisms of quasi-coherent modules on `𝒮_Y` are determined on étale charts** (the
faithfulness half of Stacks 0GQD). -/
theorem eq_of_val_app_chart {P₁ P₂ : FibredSite.quasicoherentModules.{u, u + 1, u, u} C S hS
      (spaceProj Y) (isFiberedInGroupoids_spaceProj Y)} {φ₁ φ₂ : P₁.obj ⟶ P₂.obj}
    (h : ∀ (W : Space.SmallEtale C S hS Y.1) (x),
      φ₁.val.app (op ((Space.restrictionFunctor C S hS Y.1 (spaceProj Y)
        (spacePresentation Y)).obj W)) x =
      φ₂.val.app (op ((Space.restrictionFunctor C S hS Y.1 (spaceProj Y)
        (spacePresentation Y)).obj W)) x) : φ₁ = φ₂ := by
  refine eq_of_restriction_map_eq ?_
  apply ObjectProperty.hom_ext
  rw [spaceQuasicoherentRestriction_map_hom, spaceQuasicoherentRestriction_map_hom]
  ext W x
  exact h W.unop x

/-- Morphisms of quasi-coherent modules on `𝒮_Y` are determined by their restrictions to
`Y_étale`. -/
theorem eq_of_selfChartRestrictionMap_eq {P₁ P₂ : FibredSite.quasicoherentModules.{u, u + 1, u, u}
      C S hS (spaceProj Y) (isFiberedInGroupoids_spaceProj Y)} {φ₁ φ₂ : P₁.obj ⟶ P₂.obj}
    (h : selfChartRestrictionMap (M := P₁.obj) (M' := P₂.obj) φ₁ =
      selfChartRestrictionMap (M := P₁.obj) (M' := P₂.obj) φ₂) : φ₁ = φ₂ := by
  refine eq_of_restriction_map_eq ?_
  apply ObjectProperty.hom_ext
  rwa [spaceQuasicoherentRestriction_map_hom, spaceQuasicoherentRestriction_map_hom]

/-- The restriction to `X_étale` of `k^*β` is the restriction of `β` along `k`. -/
theorem selfChartRestrictionMap_spacePullback_map (k : X ⟶ Y)
    {N N' : SheafOfModules.{u} (spaceRing Y)} (β : N ⟶ N') :
    selfChartRestrictionMap (M := (spacePullback k).obj N) (M' := (spacePullback k).obj N')
        ((spacePullback k).map β) =
      eqToHom (spaceEtaleInverseImage_eq k N).symm ≫ spaceEtaleInverseImageMap k β ≫
        eqToHom (spaceEtaleInverseImage_eq k N') := by
  ext W x
  rfl

/-- The inverse image along `k ≫ t` is the nested inverse image `k^*t^*M`. -/
theorem spacePullback_comp_obj (k : X ⟶ Y) (t : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :
    (spacePullback (k ≫ t)).obj M = (spacePullback k).obj ((spacePullback t).obj M) := rfl

/-- The restriction to `Y_étale` of `eqToHom h` is `eqToHom` of the induced equality. -/
theorem selfChartRestrictionMap_eqToHom {N₁ N₂ : SheafOfModules.{u} (spaceRing Y)} (h : N₁ = N₂) :
    selfChartRestrictionMap (M := N₁) (M' := N₂) (eqToHom h) =
      eqToHom (congrArg selfChartRestriction h) := by
  subst h
  ext W x
  rfl

/-- The comparison `compComparison k t M` is the comparison of étale inverse images along
`k ≫ t`. -/
theorem compComparison_eq (k : X ⟶ Y) (t : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :
    compComparison k t M = spaceEtaleInverseImageComparison (k ≫ t) M := rfl

/-- If `eqToHom a ≫ r ≫ eqToHom b = eqToHom c`, then `r` is itself an `eqToHom`. -/
theorem eq_eqToHom_of_eqToHom_comp_comp_eqToHom {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞}
    (a : A = B) (b : C = D) (r : B ⟶ C) (c : A = D)
    (h : eqToHom a ≫ r ≫ eqToHom b = eqToHom c) : r = eqToHom (a.symm.trans (c.trans b.symm)) := by
  subst a b
  simpa using h

/-- **The restriction of a descent morphism along `k` is a transport when the transition
reindexes to a transport along `k`.** -/
theorem restrictionMap_eq_spaceTwoMorphism (t s : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z))
    (β : (spacePullback t).obj M ⟶ (spacePullback s).obj M)
    (α : (Space.modulePullback C S hS t).obj (selfChartRestriction M) ⟶
      (Space.modulePullback C S hS s).obj (selfChartRestriction M))
    (hβ : spaceEtaleInverseImageComparison t M ≫ (spacePullbackSelfIso t M).inv ≫
      selfChartRestrictionMap β ≫ (spacePullbackSelfIso s M).hom =
        α ≫ spaceEtaleInverseImageComparison s M) (k : X ⟶ Y)
    (h₀ : k ≫ t = k ≫ s)
    (hα : (Space.modulePullbackCompIso C S hS k t).inv.app
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) ≫
        (Space.modulePullback C S hS k).map α ≫
          (Space.modulePullbackCompIso C S hS k s).hom.app
            (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) =
      Space.pullbackTransport (selfChartRestriction M) h₀)
    (hθ : ∀ W, (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj
      ((spaceFunctor k ⋙ spaceFunctor s).obj W)))
      ((eqToHom (congrArg spaceFunctor h₀).symm :
        spaceFunctor k ⋙ spaceFunctor s ⟶ spaceFunctor k ⋙ spaceFunctor t).app W))
    [IsIso (compComparison k t M)] :
    (spacePullbackRestrictionIso k t M).inv ≫ spaceEtaleInverseImageMap k β ≫
        (spacePullbackRestrictionIso k s M).hom =
      spaceTwoMorphism _ _ (isFibredOneMorphism_spaceFunctor_comp k t)
        (isFibredOneMorphism_spaceFunctor_comp k s) (eqToHom (congrArg spaceFunctor h₀).symm) hθ
        M := by
  have b : ∀ x y : (Space.modulePullback C S hS (k ≫ t)).obj (selfChartRestriction M) ⟶
      (Space.modulePullback C S hS (k ≫ s)).obj (selfChartRestriction M),
      x = y → x ≫ compComparison k s M = y ≫ compComparison k s M := fun x y h => h ▸ rfl
  have h1 := spaceEtaleInverseImageComparison_comp_restrictionMap_assoc t s M β α hβ k
  exact eq_of_comp_eq_comp_of_isIso _
    (h1.trans ((b _ _ hα).trans (pullbackTransport_comp_compComparison h₀ M hθ)))

end Spaces


end AlgebraicGeometry.Stack

end
