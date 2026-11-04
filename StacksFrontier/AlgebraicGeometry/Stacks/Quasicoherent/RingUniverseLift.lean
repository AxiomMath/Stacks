module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites

/-!
# Raising universes on a ringed site

A sheaf of modules over a sheaf of rings with sections in `Type r` can be regarded as a sheaf of
modules over the universe lift of that sheaf of rings, and conversely: restriction of scalars
along the ring isomorphism `ULift.ringEquiv` changes neither the underlying presheaf of abelian
groups nor the morphisms, so the two categories of presheaves of modules are isomorphic, not
merely equivalent. Having a global presentation and being quasi-coherent are invariant under this
change of the coefficient universe.

## Main definitions

* `SheafOfModules.uliftForPresentationSelfIso'` and
  `SheafOfModules.uliftForPresentationCompIso`: comparisons of the universe lifts of the
  sections of a sheaf of modules at different lifting amounts.
* `Stacks.Modules.ringULift`: the universe lift of a presheaf of commutative rings on a site,
  into the universe containing the site and a further parameter.
* `Stacks.Modules.presheafRingULiftDown` and `Stacks.Modules.presheafRingULiftUp`: the two
  mutually inverse functors between presheaves of modules over a presheaf of rings and over its
  universe lift, with `Stacks.Modules.presheafRingULiftEquiv` the resulting equivalence.
* `Stacks.Modules.structureSheafRingULift`, `Stacks.Modules.sheafRingULiftDown`,
  `Stacks.Modules.sheafRingULiftUp` and `Stacks.Modules.sheafRingULiftEquiv`: the same for
  sheaves of modules over the structure sheaf of a ringed site.

## Main results

* `SheafOfModules.HasGlobalPresentation.of_uliftForPresentation` and
  `SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation`: a global presentation, resp.
  quasi-coherence, of the universe lift of the sections of a sheaf of modules is one of the
  sheaf itself.
* `Stacks.Modules.isSheaf_structureRingPresheaf_ringULift`: the universe lift of a presheaf of
  commutative rings whose sets of sections form a sheaf is a sheaf of rings.
* `Stacks.Modules.presheafRingULiftDown_comp_up` and
  `Stacks.Modules.presheafRingULiftUp_comp_down`: the two functors are mutually inverse on the
  nose, and likewise `Stacks.Modules.sheafRingULiftDown_comp_up` and
  `Stacks.Modules.sheafRingULiftUp_comp_down` for sheaves.
* `Stacks.Modules.sheafRingULiftDown_over` and `Stacks.Modules.sheafRingULiftUp_over`: the
  comparison commutes with restriction to a slice site, and
  `Stacks.Modules.sheafRingULiftDown_presheaf`,
  `Stacks.Modules.sheafRingULiftUp_presheaf`: it does not change the presheaf of sections, so it
  neither creates nor destroys the sheaf condition.
* `Stacks.Modules.hasGlobalPresentation_sheafRingULiftDown`,
  `Stacks.Modules.hasGlobalPresentation_sheafRingULiftUp`,
  `Stacks.Modules.isQuasicoherentOnSite_sheafRingULiftDown` and
  `Stacks.Modules.isQuasicoherentOnSite_sheafRingULiftUp`: having a global presentation and
  being quasi-coherent are invariant under raising the universe of the coefficient rings.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r z W

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}}

universe m s t

/-- The universe lift `SheafOfModules.uliftForPresentation` of a sheaf of modules by an amount
already contained in the universe of its sections is isomorphic to the sheaf itself. -/
noncomputable def uliftForPresentationSelfIso' (M : SheafOfModules.{max t m} R) :
    uliftForPresentation.{u, v, r, max t m, t} M ≅ M :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk
      (fun X ↦ (ULift.moduleEquiv (R := R.obj.obj X) (M := M.val.obj X)).toModuleIso)
      (by intro X Y f; ext x; rfl))

/-- Two successive universe lifts of the sections of a sheaf of modules compose to the lift by
the larger amount. -/
noncomputable def uliftForPresentationCompIso (M : SheafOfModules.{m} R) :
    uliftForPresentation.{u, v, r, max s m, t} (uliftForPresentation.{u, v, r, m, s} M) ≅
      uliftForPresentation.{u, v, r, m, max t s} M :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk
      (fun X ↦ (ULift.moduleEquiv (R := R.obj.obj X)
        (M := ULift.{s} (M.val.obj X))).trans
          (ULift.moduleEquiv.trans
            (ULift.moduleEquiv (R := R.obj.obj X) (M := M.val.obj X)).symm) |>.toModuleIso)
      (by intro X Y f; ext x; rfl))

/-- Raising the universe of the sections commutes with restriction to a slice site. -/
theorem uliftForPresentation_over (M : SheafOfModules.{m} R) (Z : C) :
    (uliftForPresentation.{u, v, r, m, t} M).over Z =
      uliftForPresentation.{max u v, v, r, m, t} (M.over Z) :=
  rfl

/-- A presentation of a module by generators and relations, whose generator and target are
isomorphic to the expected ones, is a global presentation. -/
private theorem hasGlobalPresentation_of_isos {M : SheafOfModules.{m} R}
    {I K : Type (max u v r m)} {P Q X T : SheafOfModules.{max u v r m} R}
    (γ : uliftForPresentation.{u, v, r, r, max u v m} (unit R) ≅ X)
    (δ : T ≅ uliftForPresentation.{u, v, r, m, max u v r} M)
    {ι : ∀ _ : I, X ⟶ P} {κ : ∀ _ : K, X ⟶ Q} (hP : IsColimit (Cofan.mk P ι))
    (hQ : IsColimit (Cofan.mk Q κ)) {a : Q ⟶ P} {b : P ⟶ T} (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab)) : M.HasGlobalPresentation :=
  ⟨I, K, P, Q, fun i ↦ γ.hom ≫ ι i, fun k ↦ γ.hom ≫ κ k,
    ⟨isColimit_cofan_comp_iso γ ι hP⟩, ⟨isColimit_cofan_comp_iso γ κ hQ⟩,
    a, b ≫ δ.hom, by rw [← Category.assoc, hab, zero_comp], ⟨hb.ofIsoColimit (Cofork.ext δ rfl)⟩⟩

/-- A global presentation of the universe lift of the sections gives one of the module itself. -/
theorem HasGlobalPresentation.of_uliftForPresentation {M : SheafOfModules.{m} R}
    (h : (uliftForPresentation.{u, v, r, m, max u v r} M).HasGlobalPresentation) :
    M.HasGlobalPresentation := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := h
  exact hasGlobalPresentation_of_isos
    ((uliftForPresentationSelfIso'.{u, v, r, m, max u v r m}
      (uliftForPresentation.{u, v, r, r, max u v m} (unit R))).symm ≪≫
        uliftForPresentationCompIso.{u, v, r, r, max u v m, max u v r m} (unit R))
    (uliftForPresentationSelfIso'.{u, v, r, m, max u v r} _) hP hQ hab hb

/-- If the universe lift of the sections of a sheaf of modules is quasi-coherent, so is the
module itself. -/
theorem IsQuasicoherentOnSite.of_uliftForPresentation {M : SheafOfModules.{m} R}
    (h : (uliftForPresentation.{u, v, r, m, max u v r} M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I, V, f, hcover, hpres⟩ := h.locally_hasGlobalPresentation U
    exact ⟨I, V, f, hcover, fun i ↦ HasGlobalPresentation.of_uliftForPresentation (hpres i)⟩

end SheafOfModules

namespace Stacks.Modules

attribute [local implicit_reducible] ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.presheaf

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Presheaf

variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{r})

/-- The universe lift of a presheaf of commutative rings on a site, into the universe
containing the objects and the morphisms of the site, the original rings, and a further
parameter.  The algebraic structure is unchanged. -/
abbrev ringULift : Cᵒᵖ ⥤ CommRingCat.{max u v r z} :=
  𝒪 ⋙ AlgebraicGeometry.SheafOfModules.commRingCatULift.{r, max u v z}

/-- A presheaf of modules over the universe lift of a presheaf of rings, read as a presheaf of
modules over the original presheaf of rings by restriction of scalars along
`ULift.ringEquiv`. -/
noncomputable def presheafRingULiftDownObj
    (M : PresheafOfModules.{W}
      (structureRingPresheaf (ringULift.{u, v, r, z} 𝒪))) :
    PresheafOfModules.{W} (structureRingPresheaf 𝒪) :=
  letI : ∀ X, Module (ULift.{max u v z} (𝒪.obj X)) (M.presheaf.obj X) := fun X ↦
    inferInstanceAs (Module ((ringULift.{u, v, r, z} 𝒪).obj X) (M.obj X))
  letI : ∀ X, Module ((structureRingPresheaf 𝒪).obj X) (M.presheaf.obj X) := fun X ↦
    Module.compHom (R := ULift.{max u v z} (𝒪.obj X)) _
      (ULift.ringEquiv.symm.toRingHom : 𝒪.obj X →+* ULift.{max u v z} (𝒪.obj X))
  PresheafOfModules.ofPresheaf M.presheaf fun {_ _} f s x ↦ by
    apply M.map_smul f (ULift.up s) x

/-- A presheaf of modules over a presheaf of rings, read as a presheaf of modules over the
universe lift of that presheaf of rings by restriction of scalars along `ULift.ringEquiv`. -/
noncomputable def presheafRingULiftUpObj
    (N : PresheafOfModules.{W} (structureRingPresheaf 𝒪)) :
    PresheafOfModules.{W} (structureRingPresheaf (ringULift.{u, v, r, z} 𝒪)) :=
  letI : ∀ X, Module (𝒪.obj X) (N.presheaf.obj X) := fun X ↦
    inferInstanceAs (Module ((structureRingPresheaf 𝒪).obj X) (N.obj X))
  letI : ∀ X, Module ((structureRingPresheaf (ringULift.{u, v, r, z} 𝒪)).obj X)
      (N.presheaf.obj X) := fun X ↦
    Module.compHom (R := 𝒪.obj X) _
      (ULift.ringEquiv.toRingHom : ULift.{max u v z} (𝒪.obj X) →+* 𝒪.obj X)
  PresheafOfModules.ofPresheaf N.presheaf fun {_ _} f s x ↦ by
    apply N.map_smul f s.down x

/-- Restriction of scalars along the universe lift of the coefficient rings, as a functor on
presheaves of modules. -/
noncomputable def presheafRingULiftDown :
    PresheafOfModules.{W} (structureRingPresheaf (ringULift.{u, v, r, z} 𝒪)) ⥤
      PresheafOfModules.{W} (structureRingPresheaf 𝒪) where
  obj M := presheafRingULiftDownObj.{u, v, r, z} 𝒪 M
  map f := PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf
      (structureRingPresheaf (ringULift.{u, v, r, z} 𝒪))).map f)
    fun X s m ↦ by apply (f.app X).hom.map_smul (ULift.up s) m

/-- Extension of scalars along the universe lift of the coefficient rings, as a functor on
presheaves of modules; it is inverse to `Stacks.Modules.presheafRingULiftDown`. -/
noncomputable def presheafRingULiftUp :
    PresheafOfModules.{W} (structureRingPresheaf 𝒪) ⥤
      PresheafOfModules.{W}
        (structureRingPresheaf (ringULift.{u, v, r, z} 𝒪)) where
  obj N := presheafRingULiftUpObj.{u, v, r, z} 𝒪 N
  map f := PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f)
    fun X s m ↦ by apply (f.app X).hom.map_smul s.down m

/-- Lowering and then raising the coefficient universe is the identity on presheaves of
modules. -/
theorem presheafRingULiftDown_comp_up :
    presheafRingULiftDown.{u, v, r, z, W} 𝒪 ⋙ presheafRingULiftUp.{u, v, r, z, W} 𝒪 =
      Functor.id _ :=
  rfl

/-- Raising and then lowering the coefficient universe is the identity on presheaves of
modules. -/
theorem presheafRingULiftUp_comp_down :
    presheafRingULiftUp.{u, v, r, z, W} 𝒪 ⋙ presheafRingULiftDown.{u, v, r, z, W} 𝒪 =
      Functor.id _ :=
  rfl

/-- Raising the universe of the coefficient rings is an isomorphism of categories of presheaves of
modules. -/
noncomputable def presheafRingULiftEquiv :
    PresheafOfModules.{W} (structureRingPresheaf (ringULift.{u, v, r, z} 𝒪)) ≌
      PresheafOfModules.{W} (structureRingPresheaf 𝒪) where
  functor := presheafRingULiftDown.{u, v, r, z, W} 𝒪
  inverse := presheafRingULiftUp.{u, v, r, z, W} 𝒪
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Lowering the coefficient universe does not change the presheaf of sections. -/
theorem presheafRingULiftDown_presheaf
    (M : PresheafOfModules.{W}
      (structureRingPresheaf (ringULift.{u, v, r, z} 𝒪))) :
    ((presheafRingULiftDown.{u, v, r, z, W} 𝒪).obj M).presheaf = M.presheaf :=
  rfl

/-- Raising the coefficient universe does not change the presheaf of sections. -/
theorem presheafRingULiftUp_presheaf
    (N : PresheafOfModules.{W} (structureRingPresheaf 𝒪)) :
    ((presheafRingULiftUp.{u, v, r, z, W} 𝒪).obj N).presheaf = N.presheaf :=
  rfl

/-- If the presheaf of sets of sections of a presheaf of commutative rings is a sheaf, then the
universe lift of the presheaf of rings is a sheaf of rings. -/
theorem isSheaf_structureRingPresheaf_ringULift
    (hset : Presheaf.IsSheaf J (structureRingPresheaf 𝒪 ⋙ forget RingCat.{r})) :
    Presheaf.IsSheaf J (structureRingPresheaf (ringULift.{u, v, r, z} 𝒪)) := by
  have : HasLimitsOfSize.{v, max v u} CommRingCat.{max u v r z} :=
    hasLimitsOfSizeShrink.{v, max v u, max u v r z, max u v r z} _
  exact Presheaf.isSheaf_comp_of_isSheaf J (ringULift.{u, v, r, z} 𝒪)
    (forget₂ CommRingCat.{max u v r z} RingCat.{max u v r z})
    ((Presheaf.isSheaf_iff_isSheaf_comp J (ringULift.{u, v, r, z} 𝒪)
      (forget CommRingCat.{max u v r z})).mpr <|
        Presheaf.isSheaf_comp_of_isSheaf J (structureRingPresheaf 𝒪 ⋙ forget RingCat.{r})
          CategoryTheory.uliftFunctor.{max u v z, r} hset)

end Presheaf

section Sheaf

variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{r}}
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  (hset : Presheaf.IsSheaf J (structureRingPresheaf 𝒪 ⋙ forget RingCat.{r}))

/-- The structure sheaf of a ringed site with the universe of its rings raised. -/
abbrev structureSheafRingULift : Sheaf J RingCat.{max u v r z} :=
  SheafOfModules.TensorSheafification.structureSheaf (ringULift.{u, v, r, z} 𝒪)
    (isSheaf_structureRingPresheaf_ringULift.{u, v, r, z} 𝒪 hset)

/-- Restriction of scalars along the universe lift of the coefficient rings, as a functor on
sheaves of modules. -/
noncomputable def sheafRingULiftDown :
    SheafOfModules.{W} (structureSheafRingULift.{u, v, r, z} hset) ⥤
      SheafOfModules.{W} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) where
  obj M :=
    { val := (presheafRingULiftDown.{u, v, r, z, W} 𝒪).obj M.val
      isSheaf := M.isSheaf }
  map f := ⟨(presheafRingULiftDown.{u, v, r, z, W} 𝒪).map f.val⟩

/-- Extension of scalars along the universe lift of the coefficient rings, as a functor on
sheaves of modules; it is inverse to `Stacks.Modules.sheafRingULiftDown`. -/
noncomputable def sheafRingULiftUp :
    SheafOfModules.{W} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⥤
      SheafOfModules.{W} (structureSheafRingULift.{u, v, r, z} hset) where
  obj N :=
    { val := (presheafRingULiftUp.{u, v, r, z, W} 𝒪).obj N.val
      isSheaf := N.isSheaf }
  map f := ⟨(presheafRingULiftUp.{u, v, r, z, W} 𝒪).map f.val⟩

/-- Lowering and then raising the coefficient universe is the identity on sheaves of
modules. -/
theorem sheafRingULiftDown_comp_up :
    sheafRingULiftDown.{u, v, r, z, W} h𝒪 hset ⋙ sheafRingULiftUp.{u, v, r, z, W} h𝒪 hset =
      Functor.id _ :=
  rfl

/-- Raising and then lowering the coefficient universe is the identity on sheaves of
modules. -/
theorem sheafRingULiftUp_comp_down :
    sheafRingULiftUp.{u, v, r, z, W} h𝒪 hset ⋙ sheafRingULiftDown.{u, v, r, z, W} h𝒪 hset =
      Functor.id _ :=
  rfl

/-- Raising the universe of the coefficient rings is an isomorphism of categories of sheaves of
modules. -/
noncomputable def sheafRingULiftEquiv :
    SheafOfModules.{W} (structureSheafRingULift.{u, v, r, z} hset) ≌
      SheafOfModules.{W} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) where
  functor := sheafRingULiftDown.{u, v, r, z, W} h𝒪 hset
  inverse := sheafRingULiftUp.{u, v, r, z, W} h𝒪 hset
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Lowering the coefficient universe does not change the underlying presheaf of sections of a
sheaf of modules. -/
theorem sheafRingULiftDown_presheaf
    (M : SheafOfModules.{W} (structureSheafRingULift.{u, v, r, z} hset)) :
    ((sheafRingULiftDown.{u, v, r, z, W} h𝒪 hset).obj M).val.presheaf = M.val.presheaf :=
  rfl

/-- Raising the coefficient universe does not change the underlying presheaf of sections of a
sheaf of modules. -/
theorem sheafRingULiftUp_presheaf
    (N : SheafOfModules.{W} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    ((sheafRingULiftUp.{u, v, r, z, W} h𝒪 hset).obj N).val.presheaf = N.val.presheaf :=
  rfl

/-- Lowering the universe of the coefficient rings preserves zero morphisms. -/
instance preservesZeroMorphisms_sheafRingULiftDown :
    (sheafRingULiftDown.{u, v, r, z, W} h𝒪 hset).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Lowering the universe of the coefficient rings is an equivalence of categories. -/
instance isEquivalence_sheafRingULiftDown :
    (sheafRingULiftDown.{u, v, r, z, W} h𝒪 hset).IsEquivalence :=
  (sheafRingULiftEquiv.{u, v, r, z, W} h𝒪 hset).isEquivalence_functor

/-- Lowering the universe of the coefficient rings commutes with restriction to a slice site. -/
theorem sheafRingULiftDown_over (Z : C)
    (M : SheafOfModules.{W} (structureSheafRingULift.{u, v, r, z} hset)) :
    ((sheafRingULiftDown.{u, v, r, z, W} h𝒪 hset).obj M).over Z =
      (sheafRingULiftDown.{max u v, v, r, z, W}
          (J := J.over Z) (𝒪 := (Over.forget Z).op ⋙ 𝒪)
          (Sheaf.over (⟨_, h𝒪⟩ : Sheaf J RingCat.{r}) Z).property
          (Sheaf.over (⟨_, hset⟩ : Sheaf J (Type r)) Z).property).obj (M.over Z) :=
  rfl

/-- Lowering the universe of the coefficient rings turns the structure sheaf, viewed as a module
over itself, into the universe lift of the structure sheaf over the original rings. -/
theorem sheafRingULiftDown_unit :
    (sheafRingULiftDown.{u, v, r, z, max u v r z} h𝒪 hset).obj
        (SheafOfModules.unit (structureSheafRingULift.{u, v, r, z} hset)) =
      SheafOfModules.uliftForPresentation.{u, v, r, r, max u v z}
        (SheafOfModules.unit (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :=
  rfl

/-- Lowering the universe of the coefficient rings commutes with raising the universe of the
sections. -/
theorem sheafRingULiftDown_uliftForPresentation
    (M : SheafOfModules.{max u v r z} (structureSheafRingULift.{u, v, r, z} hset)) :
    (sheafRingULiftDown.{u, v, r, z, max u v r z} h𝒪 hset).obj
        (SheafOfModules.uliftForPresentation.{u, v, max u v r z, max u v r z, max u v r z} M) =
      SheafOfModules.uliftForPresentation.{u, v, r, max u v r z, max u v r z}
        ((sheafRingULiftDown.{u, v, r, z, max u v r z} h𝒪 hset).obj M) :=
  rfl

/-- A global presentation descends along the universe lift of the coefficient rings. -/
theorem hasGlobalPresentation_sheafRingULiftDown
    (M : SheafOfModules.{max u v r z} (structureSheafRingULift.{u, v, r, z} hset))
    (h : M.HasGlobalPresentation) :
    ((sheafRingULiftDown.{u, v, r, z, max u v r z} h𝒪 hset).obj M).HasGlobalPresentation := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := h
  let D := sheafRingULiftDown.{u, v, r, z, max u v r z} h𝒪 hset
  let α := SheafOfModules.uliftForPresentationCompIso.{u, v, r, r, max u v z, max u v r z}
    (SheafOfModules.unit (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
  let β : D.obj (SheafOfModules.uliftForPresentation.{u, v, max u v r z, max u v r z,
        max u v r z} M) ≅
      SheafOfModules.uliftForPresentation.{u, v, r, max u v r z, max u v r} (D.obj M) :=
    SheafOfModules.uliftForPresentationSelfIso (D.obj M) ≪≫
      (SheafOfModules.uliftForPresentationSelfIso'.{u, v, r, z, max u v r} (D.obj M)).symm
  exact SheafOfModules.hasGlobalPresentation_of_isos α.symm β
    (isColimitCofanMkObjOfIsColimit D _ ι hP) (isColimitCofanMkObjOfIsColimit D _ κ hQ)
    (by rw [← Functor.map_comp, hab, Functor.map_zero]) (isColimitCoforkMapOfIsColimit' D hab hb)

/-- Quasi-coherence descends along the universe lift of the coefficient rings. -/
theorem isQuasicoherentOnSite_sheafRingULiftDown
    (M : SheafOfModules.{max u v r z} (structureSheafRingULift.{u, v, r, z} hset))
    [M.IsQuasicoherentOnSite] :
    ((sheafRingULiftDown.{u, v, r, z, max u v r z} h𝒪 hset).obj M).IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I, V, f, hcover, hpres⟩ :=
      SheafOfModules.IsQuasicoherentOnSite.locally_hasGlobalPresentation (M := M) U
    exact ⟨I, V, f, hcover, fun i ↦ hasGlobalPresentation_sheafRingULiftDown.{max u v, v, r, z}
      (J := J.over (V i)) (𝒪 := (Over.forget (V i)).op ⋙ 𝒪)
      (Sheaf.over (⟨_, h𝒪⟩ : Sheaf J RingCat.{r}) (V i)).property
      (Sheaf.over (⟨_, hset⟩ : Sheaf J (Type r)) (V i)).property
      (M.over (V i)) (hpres i)⟩

/-- Raising the universe of the coefficient rings preserves zero morphisms. -/
instance preservesZeroMorphisms_sheafRingULiftUp :
    (sheafRingULiftUp.{u, v, r, z, W} h𝒪 hset).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Raising the universe of the coefficient rings is an equivalence of categories. -/
instance isEquivalence_sheafRingULiftUp :
    (sheafRingULiftUp.{u, v, r, z, W} h𝒪 hset).IsEquivalence :=
  (sheafRingULiftEquiv.{u, v, r, z, W} h𝒪 hset).isEquivalence_inverse

/-- Raising the universe of the coefficient rings commutes with restriction to a slice site. -/
theorem sheafRingULiftUp_over (Z : C)
    (N : SheafOfModules.{W} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    ((sheafRingULiftUp.{u, v, r, z, W} h𝒪 hset).obj N).over Z =
      (sheafRingULiftUp.{max u v, v, r, z, W}
          (J := J.over Z) (𝒪 := (Over.forget Z).op ⋙ 𝒪)
          (Sheaf.over (⟨_, h𝒪⟩ : Sheaf J RingCat.{r}) Z).property
          (Sheaf.over (⟨_, hset⟩ : Sheaf J (Type r)) Z).property).obj (N.over Z) :=
  rfl

/-- Raising the universe of the coefficient rings turns the universe lift of the structure sheaf
over the original rings into the structure sheaf over the lifted rings, viewed as a module over
itself. -/
theorem sheafRingULiftUp_uliftForPresentation_unit :
    (sheafRingULiftUp.{u, v, r, z, max u v r z} h𝒪 hset).obj
        (SheafOfModules.uliftForPresentation.{u, v, r, r, max u v z}
          (SheafOfModules.unit (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) =
      SheafOfModules.unit (structureSheafRingULift.{u, v, r, z} hset) :=
  rfl

/-- A global presentation ascends along the universe lift of the coefficient rings. -/
theorem hasGlobalPresentation_sheafRingULiftUp
    (N : SheafOfModules.{max u v r z} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (h : N.HasGlobalPresentation) :
    ((sheafRingULiftUp.{u, v, r, z, max u v r z} h𝒪 hset).obj N).HasGlobalPresentation := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := h
  let U := sheafRingULiftUp.{u, v, r, z, max u v r z} h𝒪 hset
  let α := SheafOfModules.uliftForPresentationCompIso.{u, v, r, r, max u v z, max u v r z}
    (SheafOfModules.unit (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
  let β : U.obj (SheafOfModules.uliftForPresentation.{u, v, r, max u v r z, max u v r} N) ≅
      SheafOfModules.uliftForPresentation.{u, v, max u v r z, max u v r z, max u v r z}
        (U.obj N) :=
    SheafOfModules.uliftForPresentationSelfIso'.{u, v, max u v r z, z, max u v r} (U.obj N) ≪≫
      (SheafOfModules.uliftForPresentationSelfIso (U.obj N)).symm
  exact SheafOfModules.hasGlobalPresentation_of_isos (U.mapIso α) β
    (isColimitCofanMkObjOfIsColimit U _ ι hP) (isColimitCofanMkObjOfIsColimit U _ κ hQ)
    (by rw [← Functor.map_comp, hab, Functor.map_zero]) (isColimitCoforkMapOfIsColimit' U hab hb)

/-- Quasi-coherence ascends along the universe lift of the coefficient rings. -/
theorem isQuasicoherentOnSite_sheafRingULiftUp
    (N : SheafOfModules.{max u v r z} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    [N.IsQuasicoherentOnSite] :
    ((sheafRingULiftUp.{u, v, r, z, max u v r z} h𝒪 hset).obj N).IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I, V, f, hcover, hpres⟩ :=
      SheafOfModules.IsQuasicoherentOnSite.locally_hasGlobalPresentation (M := N) U
    exact ⟨I, V, f, hcover, fun i ↦ hasGlobalPresentation_sheafRingULiftUp.{max u v, v, r, z}
      (J := J.over (V i)) (𝒪 := (Over.forget (V i)).op ⋙ 𝒪)
      (Sheaf.over (⟨_, h𝒪⟩ : Sheaf J RingCat.{r}) (V i)).property
      (Sheaf.over (⟨_, hset⟩ : Sheaf J (Type r)) (V i)).property
      (N.over (V i)) (hpres i)⟩

end Sheaf

end Stacks.Modules

end
