module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportFpqcDescent

/-!
# Proper support on an algebraic space and on its lower-shriek extension

Let `h : W ⟶ S` be a morphism of a big fppf site and `f : X ⟶ Y` a morphism of algebraic
spaces over `W`, locally of finite type.  A closed subspace of `X` extends to a closed subspace
of `Λ_h X` with the corresponding set of points, and properness is unchanged by the extension,
so a closed subset of `X` is proper over `Y` (Stacks 0CZD) exactly when its image in `Λ_h X` is
proper over `Λ_h Y`.  With the correspondence of supports of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRelocalizeSupport.lean`, an abelian sheaf (or a
module) on `X` has support proper over `Y` exactly when the corresponding one on `Λ_h X` has
support proper over `Λ_h Y`.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSubfunctorSE`: the subfunctor of `Λ_h X` cut out by a
  subfunctor of `X`, isomorphic to its extension by
  `AlgebraicGeometry.Space.relocalizeSubfunctorIsoSE`.

## Main results

* `AlgebraicGeometry.Space.isProperOver_relocalize_iffSE`: closed subsets proper over the target.
* `AlgebraicGeometry.Space.hasProperSupport_relocalize_iffSE`,
  `AlgebraicGeometry.Space.hasProperSupport_relocalizeModulesEquivalence_inverse_iffSE` and
  `AlgebraicGeometry.Space.hasProperSupport_relocalizeModulesEquivalence_functor_iffSE`: proper
  support is preserved and reflected.

## References

* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.OverShriek

/-- The lower-shriek extension of presheaves preserves monomorphisms: a section of `Λ F` is a
factorization of the structure morphism together with a section of `F` over it. -/
instance relocalizePresheafFunctor_preservesMonomorphismsSE {C : Type*} [Category.{u} C]
    {U V : C} (f : V ⟶ U) : (relocalizePresheafFunctor f).PreservesMonomorphisms where
  preserves {F G} i _ := by
    rw [NatTrans.mono_iff_mono_app]
    intro W
    rw [CategoryTheory.mono_iff_injective]
    rintro ⟨⟨a, x⟩, ha⟩ ⟨⟨b, y⟩, hb⟩ h
    have hab : a = b := congrArg (fun z => z.val.fst) h
    subst b
    have hxy : i.app (op (Over.mk a)) x = i.app (op (Over.mk a)) y :=
      eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2
    have hxy' : x = y := (CategoryTheory.mono_iff_injective (i.app _)).1 inferInstance hxy
    subst y
    rfl

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}

private instance respectsIso_inverseImage_isClosedImmersion_toScheme :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso := by
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.RespectsIso.inverseImage _ _

/-- **Closed immersions are preserved by the lower-shriek extension.** -/
theorem isClosedImmersion_relocalize_mapSE {X' : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} {k : X' ⟶ X}
    (hk : IsClosedImmersion B W hW k) :
    IsClosedImmersion B S hS ((OverShriek.relocalizePresheafFunctor h).map k) := by
  exact OverShriek.presheaf_map_relocalize h (fun _ hk' => hk') hk

/-- The subfunctor of `Λ X` cut out by a subfunctor of `X`: the image of its extension. -/
def relocalizeSubfunctorSE (Z : Subfunctor X) :
    Subfunctor ((OverShriek.relocalizePresheafFunctor h).obj X) :=
  Subfunctor.range ((OverShriek.relocalizePresheafFunctor h).map Z.ι)

/-- The extension of a subfunctor is the subfunctor it cuts out. -/
def relocalizeSubfunctorIsoSE (Z : Subfunctor X) :
    (OverShriek.relocalizePresheafFunctor h).obj Z.toFunctor ≅
      (relocalizeSubfunctorSE B W S hW hS h Z).toFunctor :=
  @asIso _ _ _ _ (Subfunctor.toRange ((OverShriek.relocalizePresheafFunctor h).map Z.ι)) 
    (@Subfunctor.instIsIsoFunctorTypeToRangeOfMono _ _ _ _ _
      (Functor.map_mono (OverShriek.relocalizePresheafFunctor h) Z.ι))

/-- The isomorphism `AlgebraicGeometry.Space.relocalizeSubfunctorIsoSE` is compatible with the
inclusions into `Λ X`. -/
theorem relocalizeSubfunctorIso_hom_ιSE (Z : Subfunctor X) :
    (relocalizeSubfunctorIsoSE B W S hW hS h Z).hom ≫ (relocalizeSubfunctorSE B W S hW hS h Z).ι =
      (OverShriek.relocalizePresheafFunctor h).map Z.ι :=
  Subfunctor.toRange_ι _

/-- **The subfunctor of `Λ X` cut out by a closed subspace of `X` is a closed subspace.** -/
theorem isClosedSubspace_relocalizeSubfunctorSE {Z : Subfunctor X}
    (hZ : IsClosedSubspace B W hW Z) :
    IsClosedSubspace B S hS (relocalizeSubfunctorSE B W S hW hS h Z) := by
  refine ⟨(isAlgebraicSpace_relocalize B ⟨W, hW⟩ ⟨S, hS⟩ h Z.toFunctor hZ.1).of_iso
    (relocalizeSubfunctorIsoSE B W S hW hS h Z), ?_⟩
  have hc := isClosedImmersion_relocalize_mapSE B W S hW hS h hZ.2
  rw [← relocalizeSubfunctorIso_hom_ιSE B W S hW hS h Z] at hc
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).1 hc

/-- The points of the subfunctor of `Λ X` cut out by a subfunctor of `X` are the points of that
subfunctor, read in `Λ X`. -/
theorem range_pointsMap_relocalizeSubfunctor_ιSE (Z : Subfunctor X) :
    Set.range (pointsMap B S hS _ (relocalizeSubfunctorSE B W S hW hS h Z).ι) =
      pointsRelocalize B W S hW hS h X '' Set.range (pointsMap B W hW _ Z.ι) := by
  have hsurj : Function.Surjective
      (pointsMap B S hS _ (relocalizeSubfunctorIsoSE B W S hW hS h Z).hom) := fun y =>
    ⟨pointsMap B S hS _ (relocalizeSubfunctorIsoSE B W S hW hS h Z).inv y, by
      rw [← Function.comp_apply
          (f := pointsMap B S hS _ (relocalizeSubfunctorIsoSE B W S hW hS h Z).hom),
        ← pointsMap_comp, Iso.inv_hom_id, pointsMap_id, id]⟩
  rw [← hsurj.range_comp, ← pointsMap_comp, relocalizeSubfunctorIso_hom_ιSE,
    ← (pointsRelocalize_surjective B W S hW hS h Z.toFunctor).range_comp, ← Set.range_comp]
  exact congrArg Set.range
    (funext fun x => (pointsRelocalize_naturality B W S hW hS h Z.ι x).symm)

variable (hX : IsAlgebraicSpace B W hW X) (hY : IsAlgebraicSpace B W hW Y) (f : X ⟶ Y)
  (hX' : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor h).obj X))
  (hY' : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor h).obj Y))

/-- **A closed subset of `X` is proper over `Y` exactly when its image in `Λ X` is proper over
`Λ Y`.** -/
theorem isProperOver_relocalize_iffSE (hf : IsLocallyOfFiniteType B W hW f)
    (Z : Set (points B W hW X)) (hZ : IsClosed Z) :
    IsProperOver B S hS (hX')
        (hY')
        ((OverShriek.relocalizePresheafFunctor h).map f)
        ((isLocallyOfFiniteType_relocalize_iff B W hW S hS h f).2 hf)
        (pointsRelocalize B W S hW hS h X '' Z)
        (isClosedMap_pointsRelocalize B W S hW hS h X Z hZ) ↔
      IsProperOver B W hW hX hY f hf Z hZ := by
  let R := reducedClosedSubspace B W hW X hX Z hZ
  have hR'c := isClosedSubspace_relocalizeSubfunctorSE B W S hW hS h
    (isClosedSubspace_reducedClosedSubspace B W hW X hX Z hZ)
  have hR'pts : Set.range (pointsMap B S hS _ (relocalizeSubfunctorSE B W S hW hS h R).ι) =
      pointsRelocalize B W S hW hS h X '' Z := by
    rw [range_pointsMap_relocalizeSubfunctor_ιSE,
      range_pointsMap_ι_reducedClosedSubspace B W hW X hX Z hZ]
  have key : IsProper B S hS ((relocalizeSubfunctorSE B W S hW hS h R).ι ≫
        (OverShriek.relocalizePresheafFunctor h).map f) ↔ IsProper B W hW (R.ι ≫ f) := by
    refine (isProper_isIso_comp_iff B S hS
      (relocalizeSubfunctorIsoSE B W S hW hS h R).hom _).symm.trans ?_
    rw [← Category.assoc, relocalizeSubfunctorIso_hom_ιSE, ← Functor.map_comp]
    exact isProper_relocalize_iff B W hW S hS h
      (isAlgebraicSpace_reducedClosedSubspace B W hW X hX Z hZ) hY (R.ι ≫ f)
  have hf' := (isLocallyOfFiniteType_relocalize_iff B W hW S hS h f).2 hf
  have hZ' := isClosedMap_pointsRelocalize B W S hW hS h X Z hZ
  exact ⟨fun hp => key.1 ((exists_isProper_closedSubspace_iff_forall B S hS hX' hY' _ hf' _ hZ').1
      ((isProper_reducedClosedSubspace_iff_exists B S hS hX' hY' _ hf' _ hZ').1 hp) _ hR'c hR'pts),
    fun hp => (isProper_reducedClosedSubspace_iff_exists B S hS hX' hY' _ hf' _ hZ').2
      ⟨_, hR'c, hR'pts, key.2 hp⟩⟩

/-- **Proper support of an abelian sheaf on `Λ X`, read on `X`.** The restriction of `M` to the
small étale site of `X` has support proper over `Y` exactly when `M` has support proper over
`Λ Y`. -/
theorem hasProperSupport_relocalize_iffSE (hf : IsLocallyOfFiniteType B W hW f)
    (M : Sheaf (SmallEtale.topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj X))
      AddCommGrpCat.{v}) :
    HasProperSupport B W hW hX hY f hf
        (((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.sheafPushforwardContinuous
          AddCommGrpCat.{v} (SmallEtale.topology B W hW X) (SmallEtale.topology B S hS _)).obj M) ↔
      HasProperSupport B S hS (hX')
        (hY')
        ((OverShriek.relocalizePresheafFunctor h).map f)
        ((isLocallyOfFiniteType_relocalize_iff B W hW S hS h f).2 hf) M := by
  have hsupp := supportOfSheaf_relocalize_eq_imageSE B W S hW hS h hX' M
  have hf' := (isLocallyOfFiniteType_relocalize_iff B W hW S hS h f).2 hf
  constructor
  · rintro ⟨hcl, hp⟩
    have hcl₁ := isClosedMap_pointsRelocalize B W S hW hS h X _ hcl
    have hcl₂ : IsClosed (supportOfSheaf B S hS _ M) := hsupp ▸ hcl₁
    exact ⟨hcl₂, isProperOver_of_eq_set B _ hS hX' hY'
      ((OverShriek.relocalizePresheafFunctor h).map f) hf' hsupp.symm hcl₁ hcl₂
      ((isProperOver_relocalize_iffSE B W S hW hS h hX hY f hX' hY' hf _ hcl).2 hp)⟩
  · rintro ⟨hcl, hp⟩
    have hcl' : IsClosed (supportOfSheaf B W hW X
        (((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.sheafPushforwardContinuous
          AddCommGrpCat.{v} (SmallEtale.topology B W hW X)
            (SmallEtale.topology B S hS _)).obj M)) := by
      rw [supportOfSheaf_relocalizeSE B W S hW hS h hX' M]
      exact hcl.preimage (continuous_pointsRelocalize B W S hW hS h X)
    exact ⟨hcl', (isProperOver_relocalize_iffSE B W S hW hS h hX hY f hX' hY' hf _ hcl').1
      (isProperOver_of_eq_set B _ hS hX' hY' ((OverShriek.relocalizePresheafFunctor h).map f) hf'
        hsupp hcl (isClosedMap_pointsRelocalize B W S hW hS h X _ hcl') hp)⟩

omit hY f hY' in
/-- The abelian sheaf of the `𝒪_X`-module attached to an `𝒪_{Λ X}`-module is the restriction of
the abelian sheaf of the latter. -/
theorem toSheaf_relocalizeModulesEquivalence_inverse_objSE
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor h).obj X)
      (hX')) :
    (SheafOfModules.toSheaf _).obj
        ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').inverse.obj M) =
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.sheafPushforwardContinuous
        AddCommGrpCat.{u} (SmallEtale.topology B W hW X) (SmallEtale.topology B S hS _)).obj
        ((SheafOfModules.toSheaf _).obj M) :=
  rfl

/-- **Proper support is invariant under relocalization**, read from `Λ X`: the `𝒪_X`-module
attached to an `𝒪_{Λ X}`-module `M` has support proper over `Y` exactly when `M` has support
proper over `Λ Y`. -/
theorem hasProperSupport_relocalizeModulesEquivalence_inverse_iffSE
    (hf : IsLocallyOfFiniteType B W hW f)
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor h).obj X)
      (hX')) :
    HasProperSupport B W hW hX hY f hf ((SheafOfModules.toSheaf _).obj
        ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').inverse.obj M)) ↔
      HasProperSupport B S hS (hX')
        (hY')
        ((OverShriek.relocalizePresheafFunctor h).map f)
        ((isLocallyOfFiniteType_relocalize_iff B W hW S hS h f).2 hf)
        ((SheafOfModules.toSheaf _).obj M) :=
  hasProperSupport_relocalize_iffSE B W S hW hS h hX hY f hX' hY' hf
    ((SheafOfModules.toSheaf _).obj M)

/-- **Proper support is invariant under relocalization.** An `𝒪_X`-module has support proper
over `Y` along `f` exactly when the corresponding `𝒪_{Λ X}`-module has support proper over
`Λ Y` along `Λ f`. -/
theorem hasProperSupport_relocalizeModulesEquivalence_functor_iffSE
    (hf : IsLocallyOfFiniteType B W hW f) (F : Modules.{u, u} B W hW X hX) :
    HasProperSupport B S hS (hX')
        (hY')
        ((OverShriek.relocalizePresheafFunctor h).map f)
        ((isLocallyOfFiniteType_relocalize_iff B W hW S hS h f).2 hf)
        ((SheafOfModules.toSheaf _).obj
          ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').functor.obj F)) ↔
      HasProperSupport B W hW hX hY f hf ((SheafOfModules.toSheaf _).obj F) := by
  refine (hasProperSupport_relocalizeModulesEquivalence_inverse_iffSE B W S hW hS h hX hY f hX' hY'
    hf ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').functor.obj F)).symm.trans ?_
  have hs : supportOfSheaf B W hW X ((SheafOfModules.toSheaf _).obj
        ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').inverse.obj
          ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').functor.obj F))) =
      supportOfSheaf B W hW X ((SheafOfModules.toSheaf _).obj F) :=
    (supportOfSheaf_eq_of_isoSheaf B W hW X hX ((SheafOfModules.toSheaf _).mapIso
      ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').unitIso.app F))).symm
  constructor
  · rintro ⟨hcl, hp⟩
    have hcl' : IsClosed (supportOfSheaf B W hW X ((SheafOfModules.toSheaf _).obj F)) := hs ▸ hcl
    exact ⟨hcl', (isProperOver_of_eq_set B _ hW hX hY f hf hs hcl hcl') hp⟩
  · rintro ⟨hcl, hp⟩
    have hcl' : IsClosed (supportOfSheaf B W hW X ((SheafOfModules.toSheaf _).obj
        ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').inverse.obj
          ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').functor.obj F)))) := hs.symm ▸ hcl
    exact ⟨hcl', (isProperOver_of_eq_set B _ hW hX hY f hf hs.symm hcl hcl') hp⟩

end AlgebraicGeometry.Space

end
