module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
import all StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective

/-!
# Total acyclicity on sites of any size: global sections and abelian direct images

Two statements of Stacks 0731 and 072Z for sites whose objects need not form a small type, as
the small étale site of an algebraic space.

* `Stacks.Cohomology.isZero_rightDerived_globalSectionsFunctor_of_isTotallyAcyclic`: part (3) of
  Stacks 0731 — a sheaf of modules whose underlying abelian sheaf is totally acyclic has
  vanishing higher right derived global sections.  Global sections are corepresented by the unit
  sheaf of modules, and `Ext` out of the unit is compared with `Ext` out of the free abelian sheaf
  on the final sheaf of sets (`Stacks.Cohomology.unitCoyonedaIsoFreeAbelianSheaf`).
* `Stacks.Cohomology.isTotallyAcyclic_abelianPushforward_of_injective`: Stacks 072Z for the
  abelian direct image — the direct image along a morphism of topoi of the abelian sheaf
  underlying an injective sheaf of modules is totally acyclic, through the adjunction of
  inverse and direct image of abelian sheaves and
  `Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`.

## Implementation notes

The second statement uses the auxiliary lemmas `isTorsionFree_abelianInverseImage`,
`isTorsionFree_freeAbelianSheaf` and `exists_extension_of_ext_one_eq_zero`, which are private to
`StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/PushforwardOfAnInjective.lean`; that
module is imported with `import all`.

## References

* [Stacks Project, Tag 0731](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Stacks.Topos.AbelianPushforward

universe x v u w v' u' w'

namespace Stacks.Cohomology

/-! ### Part (3) of Stacks 0731 on a site of any size -/

section AnySite

-- As in `Stacks.Cohomology.ObjectSections`: with module-universe-polymorphic `Abelian`
-- instances on sheaves of modules in the import closure, instance search for the abelian
-- structure at module universe `u` commits to one of those and fails on the universe constraint.
attribute [local instance 5000] SheafOfModules.instAbelian

variable {C : Type u'} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J RingCat.{u})

/-- The final presheaf of sets on a site, as a sheaf: a constant presheaf with terminal value is
a sheaf for every topology. -/
abbrev finalSheaf : Sheaf J (Type u) :=
  ⟨(Functor.const Cᵒᵖ).obj PUnit.{u + 1}, Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit⟩

/-- Morphisms out of the unit sheaf of modules are the morphisms out of the free abelian sheaf
on the final presheaf of sets into the underlying abelian sheaf: both are the global sections,
by `SheafOfModules.unitHomEquiv`, `CategoryTheory.Functor.sectionsEquivHom` and the adjunction
`Presheaf.freeAbelianSheafAdj`. -/
def unitHomEquivFreeFinal (M : SheafOfModules.{u} R) :
    (SheafOfModules.unit R ⟶ M) ≃
      ((Presheaf.freeAbelianSheaf J).obj (finalSheaf J).obj ⟶ (SheafOfModules.toSheaf R).obj M) :=
  M.unitHomEquiv.trans ((Functor.sectionsEquivHom ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
      Presheaf.forgetAbelian).obj ((SheafOfModules.toSheaf R).obj M)) PUnit).trans
    ((Presheaf.freeAbelianSheafAdj J).homEquiv (finalSheaf J).obj
      ((SheafOfModules.toSheaf R).obj M)).symm)

omit [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The value of `unitHomEquivFreeFinal` on a morphism `a` out of the unit: the adjoint
transpose of the section of `M` that `a` corresponds to. -/
lemma unitHomEquivFreeFinal_apply (M : SheafOfModules.{u} R) (a : SheafOfModules.unit R ⟶ M) :
    unitHomEquivFreeFinal J R M a =
      ((Presheaf.freeAbelianSheafAdj J).homEquiv (finalSheaf J).obj
        ((SheafOfModules.toSheaf R).obj M)).symm
        (Functor.sectionsEquivHom ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
          Presheaf.forgetAbelian).obj ((SheafOfModules.toSheaf R).obj M)) PUnit
          (M.unitHomEquiv a)) := rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- `unitHomEquivFreeFinal` is natural in the sheaf of modules: postcomposing with `p : M ⟶ N`
corresponds to postcomposing with the underlying morphism of abelian sheaves. -/
lemma unitHomEquivFreeFinal_comp {M N : SheafOfModules.{u} R}
    (a : SheafOfModules.unit R ⟶ M) (p : M ⟶ N) :
    unitHomEquivFreeFinal J R N (a ≫ p) =
      unitHomEquivFreeFinal J R M a ≫ (SheafOfModules.toSheaf R).map p := by
  rw [unitHomEquivFreeFinal_apply, unitHomEquivFreeFinal_apply,
    ← Adjunction.homEquiv_naturality_right_symm]
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- `unitHomEquivFreeFinal` is additive. -/
lemma unitHomEquivFreeFinal_add (M : SheafOfModules.{u} R) (a b : SheafOfModules.unit R ⟶ M) :
    unitHomEquivFreeFinal J R M (a + b) =
      unitHomEquivFreeFinal J R M a + unitHomEquivFreeFinal J R M b := by
  have h : ∀ c : SheafOfModules.unit R ⟶ M, unitHomEquivFreeFinal J R M c =
      unitHomEquivFreeFinal J R _ (𝟙 _) ≫ (SheafOfModules.toSheaf R).map c := fun c => by
    rw [← unitHomEquivFreeFinal_comp, Category.id_comp]
  rw [h (a + b), h a, h b, Functor.map_add, Preadditive.comp_add]

/-- The unit sheaf of modules and the sheafified free abelian presheaf on the final presheaf
corepresent the same functor on sheaves of modules, namely global sections. -/
def unitCoyonedaIsoFreeAbelianSheaf :
    preadditiveCoyoneda.obj (op (SheafOfModules.unit R)) ≅
      SheafOfModules.toSheaf R ⋙
        preadditiveCoyoneda.obj (op ((Presheaf.freeAbelianSheaf J).obj (finalSheaf J).obj)) :=
  NatIso.ofComponents
    (fun M => (AddEquiv.mk' (unitHomEquivFreeFinal J R M)
      (unitHomEquivFreeFinal_add J R M)).toAddCommGrpIso)
    (fun {M N} p => by
      ext a
      exact unitHomEquivFreeFinal_comp J R a p)

variable [HasExt.{max u' u} (Sheaf J AddCommGrpCat.{u})] [EnoughInjectives (Sheaf J
    AddCommGrpCat.{u})]
  [EnoughInjectives (SheafOfModules.{u} R)] [HasExt.{max u' u} (SheafOfModules.{u} R)]

/-- `Ext` out of the unit sheaf of modules into `M` vanishes in degree `n + 1` as soon as `Ext`
out of the free abelian sheaf on the final presheaf into the underlying abelian sheaf does.
This is the comparison of Stacks 03FD for global sections, whose acyclicity input is
`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`. -/
lemma subsingleton_ext_unit (M : SheafOfModules.{u} R) (n : ℕ)
    (hM : Subsingleton (Ext.{max u' u} ((Presheaf.freeAbelianSheaf J).obj (finalSheaf J).obj)
      ((SheafOfModules.toSheaf R).obj M) n)) :
    Subsingleton (Ext.{max u' u} (SheafOfModules.unit R) M n) := by
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) :=
    ObjectSections.toSheaf_preservesFiniteColimits J R
  have htf : ∀ U, Module.IsTorsionFree ℤ
      (((Presheaf.freeAbelianSheaf J).obj (finalSheaf J).obj).obj.obj U) :=
    ModuleSheafCohomology.isTorsionFree_sheafify J _ (fun V => by
      change Module.IsTorsionFree ℤ (FreeAbelianGroup PUnit)
      exact Module.Flat.isTorsionFree)
  let c := (ModuleSheafCohomology.extComparisonIso (SheafOfModules.toSheaf R)
    ((Presheaf.freeAbelianSheaf J).obj (finalSheaf J).obj) (SheafOfModules.unit R)
    (fun I _ m e => ObjectSections.ext_eq_zero_of_isTorsionFree J R I _ htf m e)
    (unitCoyonedaIsoFreeAbelianSheaf J R) n).app M
  exact c.addCommGroupIsoToAddEquiv.subsingleton_congr.mpr hM

/-- **Stacks 0731, part (3), on a site of any size.**  A sheaf of modules whose underlying
abelian sheaf is totally acyclic has vanishing higher right derived global sections.

Global sections are corepresented by the unit sheaf of modules
(`SheafOfModules.unitHomEquiv`), so the terms of an injective resolution of `M` are carried to
the groups of morphisms out of the unit, and the complex of global sections is exact in degree
`n + 1` because `Ext^{n+1}` out of the unit into `M` vanishes, by `subsingleton_ext_unit` and
total acyclicity at the final sheaf.  Unlike `isTotallyAcyclic_rightAcyclic_globalSections` the
site need not be small: its objects may live in a universe above its morphisms, as for the small
étale site of an algebraic space. -/
theorem isZero_rightDerived_globalSectionsFunctor_of_isTotallyAcyclic (M : SheafOfModules.{u} R)
    (hM : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj M)) (n : ℕ) (hn : 0 < n) :
    IsZero (((SiteModules.globalSectionsFunctor.{u', u, u, u} R).rightDerived n).obj M) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let I := injectiveResolution M
  let E := SiteModules.globalSectionsFunctor.{u', u, u, u} R
  let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hExt : Subsingleton (Ext.{max u' u} (SheafOfModules.unit R) M (n + 1)) :=
    subsingleton_ext_unit J R M (n + 1) (hM (finalSheaf J) (n + 1) (by omega))
  have hex : K.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    let a := (I.cocomplex.X (n + 1)).unitHomEquiv.symm x
    have hax : (I.cocomplex.X (n + 1)).unitHomEquiv a = x :=
      (I.cocomplex.X (n + 1)).unitHomEquiv.apply_symm_apply x
    have ha : a ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
      apply (I.cocomplex.X (n + 2)).unitHomEquiv.injective
      rw [SheafOfModules.unitHomEquiv_comp_apply, hax]
      exact hx.trans (Subtype.ext (funext fun X => rfl))
    have he : I.extMk a (n + 2) rfl ha = 0 := Subsingleton.elim _ _
    obtain ⟨b, hb⟩ := (I.extMk_eq_zero_iff a (n + 2) rfl ha n rfl).mp he
    refine ⟨(I.cocomplex.X n).unitHomEquiv b, ?_⟩
    change SheafOfModules.sectionsMap (I.cocomplex.d n (n + 1)) _ = x
    rw [← SheafOfModules.unitHomEquiv_comp_apply, hb, hax]
  exact hex.isZero_homology.of_iso (I.isoRightDerivedObj E (n + 1))

end AnySite

/-! ### The direct image of the abelian sheaf underlying an injective module -/

section AbelianPushforward

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (φ : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})] [HasSheafify K AddCommGrpCat.{w'}]
  [HasExt.{x} (Sheaf K AddCommGrpCat.{w'})] [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{w'})]
  (R : Sheaf J RingCat.{w}) (I : SheafOfModules.{w} R) [Injective I]

/-- **The core of Stacks 072Z, on sites of any size.**  Let `φ` be a morphism of topoi and `I`
an injective sheaf of modules on its source.  Then `Ext` out of a sectionwise torsion-free
abelian sheaf into the direct image of the abelian sheaf underlying `I` vanishes in positive
degree.

The dévissage `ModuleSheafCohomology.ext_eq_zero_of_resolving` reduces to degree one, where the
adjunction `φ⁻¹ ⊣ φ_*` of abelian sheaves turns the extension problem into one on the source;
there the exact inverse image has produced a short exact sequence with torsion-free third term,
against which the underlying abelian sheaf of an injective module is `Ext`-acyclic,
`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`.  Neither site is assumed small,
and the four universes of the two sites and of their sheaves are independent. -/
theorem ext_eq_zero_abelianPushforward_of_isTorsionFree
    (T : Sheaf K AddCommGrpCat.{w'}) (hT : ∀ U, Module.IsTorsionFree ℤ (T.obj.obj U)) (n : ℕ)
    (a : Ext.{x} T ((abelianPushforward J φ).obj ((SheafOfModules.toSheaf R).obj I)) (n + 1)) :
    a = 0 := by
  have := HasExt.standard (Sheaf J AddCommGrpCat.{w})
  let adj := abelianInverseImageAdjPushforward J φ
  apply ModuleSheafCohomology.ext_eq_zero_of_resolving
    (fun G : Sheaf K AddCommGrpCat.{w'} => ∀ U, Module.IsTorsionFree ℤ (G.obj.obj U))
    ?_ (ModuleSheafCohomology.exists_isTorsionFree_epi K) _ ?_ n T hT a
  · intro G H m _ hH
    exact ModuleSheafCohomology.isTorsionFree_of_mono K m hH
  · apply ModuleSheafCohomology.ext_one_eq_zero_of_extension
    intro S hS hP m
    obtain ⟨g, hg⟩ := exists_extension_of_ext_one_eq_zero
      (ShortComplex.ShortExact.map_of_exact hS (Sites.abelianInverseImage φ)) _
      (fun e => ObjectSections.ext_eq_zero_of_isTorsionFree J R I _
        (isTorsionFree_abelianInverseImage φ S.X₃ hP) 0 e)
      ((adj.homEquiv _ _).symm m)
    have hg' : (Sites.abelianInverseImage φ).map S.f ≫ g = (adj.homEquiv _ _).symm m := hg
    exact ⟨adj.homEquiv _ _ g, by
      rw [← adj.homEquiv_naturality_left, hg', Equiv.apply_symm_apply]⟩

/-- **Stacks 072Z for the abelian direct image, on sites of any size.**  The direct image along a
morphism of topoi of the abelian sheaf underlying an injective sheaf of modules is totally
acyclic.  The free abelian sheaf on a sheaf of sets is sectionwise torsion free, so this is
`Stacks.Cohomology.ext_eq_zero_abelianPushforward_of_isTorsionFree`. -/
theorem isTotallyAcyclic_abelianPushforward_of_injective :
    IsTotallyAcyclic K ((abelianPushforward J φ).obj ((SheafOfModules.toSheaf R).obj I)) := by
  intro T p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact subsingleton_of_forall_eq 0 (ext_eq_zero_abelianPushforward_of_isTorsionFree φ R I _
    (isTorsionFree_freeAbelianSheaf K T) n)

end AbelianPushforward

end Stacks.Cohomology

end
