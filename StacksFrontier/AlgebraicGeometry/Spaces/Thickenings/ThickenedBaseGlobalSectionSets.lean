module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRestrictionInverseImageGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedFirstOrderExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickenedBasePushoutQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalModuleInverseImageKernel

/-!
# The thickened base `(f ≫ i)⁻¹𝒪_{D'} ≅ f⁻¹𝒜` on inverse images of global sections

For morphisms of algebraic spaces `f : X ⟶ D`, `i : D ⟶ D'` and a sheaf of rings `𝒜` on `D`
identified with `i⁻¹𝒪_{D'}`, the identification
`AlgebraicGeometry.Space.thickenedBaseIso : (f ≫ i)⁻¹𝒪_{D'} ≅ f⁻¹𝒜` carries the inverse image along
`f` of a global section `β` of `𝒜` which is `i⁻¹τ` for a global section `τ` of `𝒪_{D'}` to the
inverse image of `τ` along `f ≫ i`, on underlying sheaves of sets. Followed by the maps
`(f ≫ i)⁻¹𝒪_{D'} ⟶ a⁻¹𝒪_W` for `a ≫ g = f ≫ i` and `a⁻¹𝒪_W ≅ (ι⁻¹𝒪_W)|_X` for `a = ρ ≫ ι`
through a closed subspace, it is the restriction along `ρ` of the inverse image along `ι` of the
global section `g^♯(g⁻¹τ)`. This is the comparison of the base map of the extension problem of
the body of the proof of [Stacks Project, Tag 0D3X] with the tower of thickenings, on the sections
given by functions of the base.

## Main results

* `CategoryTheory.sheafCompose_forget_map_sheafCompose_forget₂_map`: the underlying sheaf of sets
  of a morphism of sheaves of commutative rings, read through the sheaves of rings.

In the namespace `AlgebraicGeometry.Space`:

* `globalSectionMap_comp_forget_map_thickenedBaseIso_inv`: `f⁻¹(i⁻¹τ)` is carried by
  `f⁻¹𝒜 ≅ (f ≫ i)⁻¹𝒪_{D'}` to `(f ≫ i)⁻¹τ`.
* `globalSectionMap_comp_forget_map_thickenedBaseIso_inv_comp_inverseImageStructureSheafMapOfEq`:
  followed by `(f ≫ i)⁻¹𝒪_{D'} ⟶ a⁻¹𝒪_W`, it becomes `a⁻¹(g^♯(g⁻¹τ))`.
* `globalSectionMap_comp_forget_map_eqToIso_trans_etaleRestrictionRingComparison_α_hom`:
  `a⁻¹𝒪_W ≅ (ι⁻¹𝒪_W)|_X` carries `a⁻¹t` to the restriction along `ρ` of `ι⁻¹t`.
* `globalSectionMap_comp_forget_map_thickenedBaseIso_inv_comp_etaleRestrictionRingComparison_α`:
  the composite carries `f⁻¹β` to the restriction along `ρ` of `ι⁻¹(g^♯(g⁻¹τ))`.
* `globalSectionMap_comp_forget_map_restrictedFirstOrderExtensionIso_inv_comp_eqToHom`: for a
  first order thickening, the restriction along `ρ` of `ι⁻¹t` is carried to `j⁻¹t`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace CategoryTheory

/-- The underlying sheaf of sets of a morphism of sheaves of commutative rings, read through the
sheaves of rings. -/
theorem sheafCompose_forget_map_sheafCompose_forget₂_map {C : Type*} [Category C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget CommRingCat.{u})]
    {A A' : Sheaf J CommRingCat.{u}} (φ : A ⟶ A') :
    (sheafCompose J (forget RingCat.{u})).map
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ) =
      (sheafCompose J (forget CommRingCat.{u})).map φ :=
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X D D' : AlgebraicSpaces B S hS} (f : X ⟶ D) (i : D ⟶ D')
  {𝒜 : Sheaf (SmallEtale.topology B S hS D.1) CommRingCat.{u}}
  (e : 𝒜 ≅ inverseImageStructureSheaf B S hS i)
  (τ : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS D'.1) (forget CommRingCat.{u})).obj
    (smallEtaleRingedTopos B S hS D').O)
  (β : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS D.1) (forget CommRingCat.{u})).obj 𝒜)

/-- The composition isomorphism of inverse images of sheaves of commutative rings is, on
underlying sheaves of sets, the composition isomorphism of inverse images. -/
theorem forget_map_smallEtaleRingedToposHom_compInverseImageRingIso_hom_app :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS f i).hom.app
          (smallEtaleRingedTopos B S hS D').O) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS f i).hom.app
        ((sheafCompose (SmallEtale.topology B S hS D'.1) (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS D').O) := by
  rw [smallEtaleRingedToposHom_compInverseImageRingIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.map_comp]
  exact (congrArg (· ≫ _)
    (Stacks.Sheaves.ToposPushforward.forget_map_inverseImageCommRingComp_hom
      (smallEtaleRingedToposHom B S hS i).toToposHom (smallEtaleRingedToposHom B S hS f).toToposHom
      (smallEtaleRingedTopos B S hS D').O)).trans (Category.id_comp _)

/-- **`f⁻¹𝒜 ≅ (f ≫ i)⁻¹𝒪_{D'}` on underlying sheaves of sets**: the inverse image along `f` of
`𝒜 ≅ i⁻¹𝒪_{D'}` followed by the composition isomorphism of inverse images. -/
theorem forget_map_thickenedBaseIso_inv :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
        (thickenedBaseIso B S hS f i e).inv =
      (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
          ((sheafCompose (SmallEtale.topology B S hS D.1) (forget CommRingCat.{u})).map e.hom) ≫
        (smallEtaleRingedToposHom_compInverseImageIso B S hS f i).hom.app
          ((sheafCompose (SmallEtale.topology B S hS D'.1) (forget CommRingCat.{u})).obj
            (smallEtaleRingedTopos B S hS D').O) :=
  ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map_comp _ _).trans
    (congrArg₂ (· ≫ ·)
      (Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap
        (SmallEtale.topology B S hS X.1)
        (Φ := (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage) e.hom)
      (forget_map_smallEtaleRingedToposHom_compInverseImageRingIso_hom_app B S hS f i))

/-- **The thickened base on inverse images of global sections**: if a global section `β` of `𝒜`
is, through `𝒜 ≅ i⁻¹𝒪_{D'}`, the inverse image of a global section `τ` of `𝒪_{D'}`, then
`f⁻¹β`, read through `f⁻¹𝒜 ≅ (f ≫ i)⁻¹𝒪_{D'}`, is the inverse image of `τ` along `f ≫ i`, on
underlying sheaves of sets. -/
theorem globalSectionMap_comp_forget_map_thickenedBaseIso_inv
    (hβ : β ≫ (sheafCompose (SmallEtale.topology B S hS D.1) (forget CommRingCat.{u})).map e.hom =
      (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.globalSectionMap τ) :
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.globalSectionMap β ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
          (thickenedBaseIso B S hS f i e).inv =
      (smallEtaleRingedToposHom B S hS (f ≫ i)).toToposHom.inverseImage.globalSectionMap τ := by
  have s3 : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.globalSectionMap β ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
          ((sheafCompose (SmallEtale.topology B S hS D.1) (forget CommRingCat.{u})).map e.hom) =
      (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.globalSectionMap
        ((smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.globalSectionMap τ) :=
    (Functor.globalSectionMap_comp (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage β
      ((sheafCompose (SmallEtale.topology B S hS D.1) (forget CommRingCat.{u})).map e.hom)).trans
      (congrArg (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.globalSectionMap hβ)
  have s4 : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.globalSectionMap
        ((smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.globalSectionMap τ) ≫
        (smallEtaleRingedToposHom_compInverseImageIso B S hS f i).hom.app
          ((sheafCompose (SmallEtale.topology B S hS D'.1) (forget CommRingCat.{u})).obj
            (smallEtaleRingedTopos B S hS D').O) =
      (smallEtaleRingedToposHom B S hS (f ≫ i)).toToposHom.inverseImage.globalSectionMap τ :=
    Functor.globalSectionMap_globalSectionMap_comp_app
      (smallEtaleRingedToposHom_compInverseImageIso B S hS f i).hom τ
  have s5 : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.globalSectionMap β ≫
        ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
            ((sheafCompose (SmallEtale.topology B S hS D.1) (forget CommRingCat.{u})).map e.hom) ≫
          (smallEtaleRingedToposHom_compInverseImageIso B S hS f i).hom.app
            ((sheafCompose (SmallEtale.topology B S hS D'.1) (forget CommRingCat.{u})).obj
              (smallEtaleRingedTopos B S hS D').O)) =
      (smallEtaleRingedToposHom B S hS (f ≫ i)).toToposHom.inverseImage.globalSectionMap τ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫
      (smallEtaleRingedToposHom_compInverseImageIso B S hS f i).hom.app
        ((sheafCompose (SmallEtale.topology B S hS D'.1) (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS D').O)) s3).trans s4)
  exact (congrArg
    ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.globalSectionMap β ≫ ·)
    (forget_map_thickenedBaseIso_inv B S hS f i e)).trans s5

/-- If `x ≫ F.map φ = y` and `y ≫ F.map ψ = w`, then `x ≫ F.map (φ ≫ ψ) = w`. -/
private theorem comp_map_comp_eq_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {T : D} {A B E : C} {x : T ⟶ F.obj A} {y : T ⟶ F.obj B} {w : T ⟶ F.obj E} {φ : A ⟶ B}
    {ψ : B ⟶ E} (h₁ : x ≫ F.map φ = y) (h₂ : y ≫ F.map ψ = w) : x ≫ F.map (φ ≫ ψ) = w := by
  rw [F.map_comp, ← Category.assoc, h₁, h₂]

/-- **The thickened base followed by `(f ≫ i)⁻¹𝒪_{D'} ⟶ a⁻¹𝒪_W`, on inverse images of global
sections**: for `a ≫ g = f ≫ i`, the inverse image `f⁻¹β` of a global section `β = i⁻¹τ` of `𝒜`
is carried to the inverse image along `a` of the global section `g^♯(g⁻¹τ)` of `𝒪_W`. -/
theorem globalSectionMap_comp_forget_map_thickenedBaseIso_inv_comp_inverseImageStructureSheafMapOfEq
    {W : AlgebraicSpaces B S hS} (a : X ⟶ W) (g : W ⟶ D') (hc : a ≫ g = f ≫ i)
    (hβ : β ≫ (sheafCompose (SmallEtale.topology B S hS D.1) (forget CommRingCat.{u})).map e.hom =
      (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.globalSectionMap τ) :
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.globalSectionMap β ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
          ((thickenedBaseIso B S hS f i e).inv ≫ inverseImageStructureSheafMapOfEq B S hS a g hc) =
      (smallEtaleRingedToposHom B S hS a).toToposHom.inverseImage.globalSectionMap
        ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.globalSectionMap τ ≫
          (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
            (structureSharpInverseImage B S hS g)) := by
  rw [show inverseImageStructureSheafMapOfEq B S hS a g hc =
      eqToHom (congrArg (inverseImageStructureSheaf B S hS) hc.symm) ≫
        inverseImageStructureSheafMap B S hS a g from rfl]
  refine comp_map_comp_eq_of_eq (sheafCompose _ _)
    (globalSectionMap_comp_forget_map_thickenedBaseIso_inv B S hS f i e τ β hβ) ?_
  exact comp_map_comp_eq_of_eq (sheafCompose _ _)
    (globalSectionMap_comp_forget_map_eqToHom_inverseImageStructureSheaf B S hS hc.symm τ)
    (globalSectionMap_comp_forget_map_inverseImageStructureSheafMap B S hS a g τ)

/-- For an isomorphism `ρ : X ≅ Z` onto a closed subspace, postcomposition with `ρ` is continuous
for the small étale topologies of `X` and `Z`. -/
local instance instIsContinuousSmallEtalePostcompThickenedBaseGlobalSectionSets
    {W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS W.1)
    (ρ : X ≅ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :
    (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS _)).IsContinuous
      (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) :=
  smallEtalePostcomp_isContinuous B S hS _ _

/-- **`a⁻¹𝒪_W ≅ (ι⁻¹𝒪_W)|_X` on inverse images of global sections**, for `a = ρ ≫ ι` through a
closed subspace `ι : Z ⟶ W` and `ρ : X ≅ Z`: the inverse image along `a` of a global section `t`
of `𝒪_W` is the restriction along `ρ` of its inverse image along `ι`, on underlying sheaves of
sets. -/
theorem globalSectionMap_comp_forget_map_eqToIso_trans_etaleRestrictionRingComparison_α_hom
    {W : AlgebraicSpaces B S hS} (a : X ⟶ W) (Z : ClosedSubspaces B S hS W.1)
    (ρ : X ≅ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (ha : ρ.hom ≫ subspaceInclusion B S hS W Z = a)
    (t : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS W).O) :
    (smallEtaleRingedToposHom B S hS a).toToposHom.inverseImage.globalSectionMap t ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
          (eqToIso (congrArg (inverseImageStructureSheaf B S hS) ha.symm) ≪≫
            (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS _)
              (subspaceInclusion B S hS W Z)).α).hom =
      (smallEtaleSetRestriction B S hS ρ.hom (isEtale_hom_of_iso B S hS _)).globalSectionMap
        ((thickeningToposHom B S hS Z).inverseImage.globalSectionMap t) := by
  refine comp_map_comp_eq_of_eq (sheafCompose _ _)
    (globalSectionMap_comp_forget_map_eqToHom_inverseImageStructureSheaf B S hS ha.symm t) ?_
  exact (globalSectionMap_comp_forget_map_etaleRestrictionRingComparison_α_hom B S hS ρ.hom
      (isEtale_hom_of_iso B S hS _) (subspaceInclusion B S hS W Z) t)

/-- **The thickened base followed by `(f ≫ i)⁻¹𝒪_{D'} ⟶ a⁻¹𝒪_W ≅ (ι⁻¹𝒪_W)|_X`, on inverse images
of global sections**: for `a ≫ g = f ≫ i` and `a = ρ ≫ ι` through a closed subspace `ι : Z ⟶ W`,
the inverse image `f⁻¹β` of a global section `β = i⁻¹τ` of `𝒜` is carried to the restriction
along `ρ` of the inverse image along `ι` of the global section `g^♯(g⁻¹τ)` of `𝒪_W`. -/
theorem globalSectionMap_comp_forget_map_thickenedBaseIso_inv_comp_etaleRestrictionRingComparison_α
    {W : AlgebraicSpaces B S hS} (a : X ⟶ W) (g : W ⟶ D') (hc : a ≫ g = f ≫ i)
    (Z : ClosedSubspaces B S hS W.1) (ρ : X ≅ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (ha : ρ.hom ≫ subspaceInclusion B S hS W Z = a)
    (hβ : β ≫ (sheafCompose (SmallEtale.topology B S hS D.1) (forget CommRingCat.{u})).map e.hom =
      (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.globalSectionMap τ) :
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.globalSectionMap β ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
          ((thickenedBaseIso B S hS f i e).inv ≫
            inverseImageStructureSheafMapOfEq B S hS a g hc ≫
              (eqToIso (congrArg (inverseImageStructureSheaf B S hS) ha.symm) ≪≫
                (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS _)
                  (subspaceInclusion B S hS W Z)).α).hom) =
      (smallEtaleSetRestriction B S hS ρ.hom (isEtale_hom_of_iso B S hS _)).globalSectionMap
        ((thickeningToposHom B S hS Z).inverseImage.globalSectionMap
          ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.globalSectionMap τ ≫
            (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
              (structureSharpInverseImage B S hS g))) := by
  refine (congrArg (fun φ => _ ≫ (sheafCompose _ _).map φ) (Category.assoc _ _ _).symm).trans ?_
  refine comp_map_comp_eq_of_eq (sheafCompose _ _)
    (globalSectionMap_comp_forget_map_thickenedBaseIso_inv_comp_inverseImageStructureSheafMapOfEq
      B S hS f i e τ β a g hc hβ) ?_
  exact (globalSectionMap_comp_forget_map_eqToIso_trans_etaleRestrictionRingComparison_α_hom
      B S hS a Z ρ ha _)

/-- **The restricted extension of a first order thickening on inverse images of global
sections**: for a first order thickening `ι : Z ⟶ Y`, `ρ : U ≅ Z` and `j = ρ ≫ ι`, the restriction
along `ρ` of the inverse image along `ι` of a global section `t` of `𝒪_Y`, read in `j⁻¹𝒪_Y` through
`(ρ ≫ ι)⁻¹𝒪_Y ≅ (ι⁻¹𝒪_Y)|_U`, is the inverse image of `t` along `j`, on underlying sheaves of
sets. -/
theorem globalSectionMap_comp_forget_map_restrictedFirstOrderExtensionIso_inv_comp_eqToHom
    {Y Y' U : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS Y.1)
    (hZ : IsFirstOrderThickening B S hS Y Z.1)
    (ρ : U ≅ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) (h : Y ⟶ Y') {j : U ⟶ Y}
    (hj : ρ.hom ≫ subspaceInclusion B S hS Y Z = j)
    (t : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS Y).O) :
    (smallEtaleSetRestriction B S hS ρ.hom (isEtale_hom_of_iso B S hS _)).globalSectionMap
        ((thickeningToposHom B S hS Z).inverseImage.globalSectionMap t) ≫
      (sheafCompose (SmallEtale.topology B S hS U.1) (forget CommRingCat.{u})).map
        ((restrictedFirstOrderExtensionIso B S hS Z hZ ρ h).inv ≫
          eqToHom (congrArg (inverseImageStructureSheaf B S hS) hj)) =
      (smallEtaleRingedToposHom B S hS j).toToposHom.inverseImage.globalSectionMap t := by
  have hα := globalSectionMap_comp_forget_map_etaleRestrictionRingComparison_α_hom B S hS ρ.hom
    (isEtale_hom_of_iso B S hS _) (subspaceInclusion B S hS Y Z) t
  have s1 := (((sheafCompose _ _).mapIso (etaleRestrictionRingComparison B S hS ρ.hom
    (isEtale_hom_of_iso B S hS _) (subspaceInclusion B S hS Y Z)).α).eq_comp_inv.2 hα).symm
  exact comp_map_comp_eq_of_eq (sheafCompose _ _) s1
    (globalSectionMap_comp_forget_map_eqToHom_inverseImageStructureSheaf B S hS hj t)

end AlgebraicGeometry.Space

end
