module

public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteProEtaleSerre
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleComplexes
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Annihilator
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantQuotient

/-!
# The completed constant sheaf on the small pro-étale site is derived complete

Let `X` be a scheme, `Λ` a ring and `I ⊂ Λ` an ideal. On `X_proétale`, ringed by the constant
sheaf `Λ̲`, the completed constant sheaf `Λ̲^∧ = lim (Λ/Iⁿ)̲` is derived complete along the ideal
sheaf `IΛ̲`. This is part (3) of [Stacks, Tag 099Q] on the small pro-étale site.

The proof is the source's: `Λ̲^∧` is the limit of the constant sheaves `(Λ/Iⁿ)̲`, each of which
is derived complete because the `n`-th power of every local section of `IΛ̲` kills it, and a limit
of derived complete sheaves is derived complete (part (4)).

## Main definitions

* `AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctorCompToSheafIso`: reading a
  sheaf of `Λ`-modules as a sheaf of `Λ̲`-modules does not change its underlying abelian sheaf.

## Main results

* `PresheafOfModules.Sheafify.smul_app_eq_zero`: on the sheafification of a presheaf of modules,
  the image of a section of the presheaf of rings acts as zero if that section acts as zero
  before sheafifying.
* `AlgebraicGeometry.ProEtale.pow_mem_annihilatorObj_of_mem_constantCoefficientIdealSheaf`: if
  `Iⁿ` kills a sheaf of `Λ`-modules `𝒢`, then the `n`-th power of every local section of `IΛ̲`
  annihilates `𝒢` read as a sheaf of `Λ̲`-modules.
* `AlgebraicGeometry.ProEtale.preservesLimitsOfShape_moduleSheafOverConstantCoefficientsFunctor`:
  reading sheaves of `Λ`-modules as sheaves of `Λ̲`-modules preserves small limits.
* `AlgebraicGeometry.ProEtale.isDerivedComplete_completedConstantSheaf_proetale`: part (3) of
  [Stacks, Tag 099Q] on the small pro-étale site.

## Implementation notes

`Λ̲^∧` is `Stacks.ConstantSheaf.completedConstantSheaf`, the limit in sheaves of `Λ`-modules of
the constant sheaves `(Λ/Iⁿ)̲`, read as a sheaf of modules over the constant coefficient ring
sheaf by `AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctor`. That functor is
a sheafification, so it is not evidently compatible with limits; it is, because it does not change
the underlying abelian sheaf and the forgetful functor from sheaves of modules to abelian sheaves
preserves and reflects limits.

The ring `Λ` lies in `Type (u + 1)`, the universe of the sections of sheaves on the small
pro-étale site of `X : Scheme.{u}`, as `Stacks.ConstantSheaf.completedConstantSheaf` requires.

Neither the Noetherian hypothesis of the source nor finite generation of `I` is used: that a
local section `f` of `IΛ̲` has `fⁿ` killing `(Λ/Iⁿ)̲` is checked locally, where `f` is the image of
an element of `I`.

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
* [Stacks Project, Tag 093M](https://stacks.math.columbia.edu/tag/093M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v v' u u'

namespace PresheafOfModules.Sheafify

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  {M₀ : PresheafOfModules.{v} R₀} {A : Sheaf J AddCommGrpCat.{v}}
  (φ : M₀.presheaf ⟶ A.obj)
  [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]

/-- On the sheafification of a presheaf of modules, the image of a section `r₀` of the presheaf
of rings acts as zero as soon as the restrictions of `r₀` act as zero on the presheaf of
modules. -/
theorem smul_app_eq_zero {X : Cᵒᵖ} (r₀ : R₀.obj X) (m : A.obj.obj X)
    (h : ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (m₀ : M₀.obj Y), R₀.map f r₀ • m₀ = 0) :
    smul α φ (α.app X r₀) m = 0 := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [map_smul_eq α φ (α.app X r₀) m f.op (R₀.map f.op r₀)
    (by rw [← RingCat.comp_apply, α.naturality, RingCat.comp_apply]) m₀ hm₀, h f.op m₀]
  exact ((φ.app (op Y)).hom.map_zero).trans ((A.obj.map f.op).hom.map_zero).symm

end PresheafOfModules.Sheafify

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

section Comparison

attribute [local instance] SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

/-- A scalar `a ∈ Λ` acting as zero on a sheaf of `Λ`-modules `𝒢` acts as zero on `𝒢` read as a
sheaf of modules over the constant coefficient ring sheaf, through its image in `Λ̲`. -/
theorem smul_moduleSheafOverConstantCoefficients_eq_zero
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) (a : Λ)
    (ha : ∀ (V : X.ProEtᵒᵖ) (s : G.obj.obj V), a • s = 0) {W : X.ProEtᵒᵖ}
    (y : ((moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ).obj G).val.obj W) :
    (constantCoefficientRingMap.{u, u + 1, u} X Λ).app W (ULift.up a) • y = 0 :=
  PresheafOfModules.Sheafify.smul_app_eq_zero _ _ _ _ fun _ _ m₀ => ha _ m₀

/-- **Powers of local sections of `IΛ̲` annihilate a sheaf of modules killed by a power of `I`.**
If `Iⁿ` kills a sheaf of `Λ`-modules `𝒢`, then for every local section `f` of the ideal sheaf
`IΛ̲`, the power `fⁿ` annihilates `𝒢` read as a sheaf of `Λ̲`-modules. Locally `f` is the image of
some `c ∈ Λ`, and wherever `f` comes from `Λ` and dies in `(Λ/I)̲`, the element `c` lies in `I`. -/
theorem pow_mem_annihilatorObj_of_mem_constantCoefficientIdealSheaf (I : Ideal Λ) (n : ℕ)
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hG : ∀ a ∈ I ^ n, ∀ (V : X.ProEtᵒᵖ) (s : G.obj.obj V), a • s = 0) {U : X.ProEtᵒᵖ}
    {f : (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, u + 1, u} X Λ).O).obj.obj U}
    (hf : f ∈ (constantCoefficientIdealSheaf.{u, u + 1, u} X Λ I).obj U) :
    f ^ n ∈ SheafOfModules.annihilatorObj
      ((moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ).obj G) U := by
  let α := constantCoefficientRingMap.{u, u + 1, u} X Λ
  let α' := constantCoefficientRingMap.{u, u + 1, u} X (Λ ⧸ I)
  let R := Stacks.SheafOfModules.Tensor.ringSheaf
    (constantCoefficientRingedSite.{u, u + 1, u} X Λ).O
  refine SheafOfModules.mem_annihilatorObj_of_locally _ _
    (Presheaf.imageSieve_mem (Scheme.ProEt.topology X) α f) ?_
  rintro Y g ⟨c, hc⟩
  have hred : ∀ (V : X.ProEtᵒᵖ) (b : ULift.{u + 1} Λ),
      (constantCoefficientRingReduction.{u, u + 1, u} X Λ I).hom.app V (α.app V b) =
        α'.app V (ULift.up (Ideal.Quotient.mk I b.down)) := by
    intro V b
    exact (congrArg (fun φ => ((forget₂ CommRingCat RingCat).map (φ.app V)).hom b)
      (toSheafify_naturality (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom
          ((ULift.ringEquiv.{u + 1, max (u + 1) u} (R := Λ ⧸ I)).symm.toRingHom.comp
            ((Ideal.Quotient.mk I).comp
              (ULift.ringEquiv.{u + 1, max (u + 1) u} (R := Λ)).toRingHom)))))).symm
  have hc' : α'.app (op Y) (ULift.up (Ideal.Quotient.mk I c.down)) = α'.app (op Y) 0 := by
    rw [← hred, hc, map_zero, ← RingCat.comp_apply,
      (constantCoefficientRingReduction.{u, u + 1, u} X Λ I).hom.naturality,
      RingCat.comp_apply, RingHom.mem_ker.1 ((SheafOfModules.mem_kerIdeal _ U f).1 hf), map_zero]
  refine SheafOfModules.mem_annihilatorObj_of_locally _ _
    (Presheaf.equalizerSieve_mem (Scheme.ProEt.topology X) α' _ _ hc') ?_
  intro Z h hh
  have hcI : c.down ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (congrArg ULift.down hh)
  have e : R.obj.map h.op (R.obj.map g.op (f ^ n)) = α.app (op Z) (c ^ n) := by
    rw [map_pow, map_pow, ← hc, ← RingCat.comp_apply, ← α.naturality, map_pow]
    rfl
  rw [e]
  intro W' g' y
  rw [← RingCat.comp_apply, ← α.naturality]
  exact smul_moduleSheafOverConstantCoefficients_eq_zero X Λ G (c.down ^ n)
    (hG _ (Ideal.pow_mem_pow hcI n)) y


/-- The underlying presheaf of abelian groups of a sheaf of `Λ`-modules read as a presheaf of
modules over the constant presheaf of coefficient rings is its own underlying presheaf. -/
def modulePresheafOverConstantCoefficientsCompToPresheafIso :
    modulePresheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ ⋙
        PresheafOfModules.toPresheaf _ ≅
      sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ sheafToPresheaf _ _ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **Reading a sheaf of `Λ`-modules as a sheaf of `Λ̲`-modules does not change its underlying
abelian sheaf.** The sheafification involved is that of a presheaf which is already a sheaf. -/
def moduleSheafOverConstantCoefficientsFunctorCompToSheafIso :
    moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ ⋙
        SheafOfModules.toSheaf.{u + 1} _ ≅
      sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  (Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (modulePresheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ)
      (PresheafOfModules.sheafificationCompToSheaf.{u + 1}
        (constantCoefficientRingMap.{u, u + 1, u} X Λ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (modulePresheafOverConstantCoefficientsCompToPresheafIso X Λ) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sheafificationNatIso _ _).symm ≪≫
    Functor.rightUnitor _ :
      (modulePresheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ ⋙
        PresheafOfModules.sheafification (constantCoefficientRingMap.{u, u + 1, u} X Λ)) ⋙
          SheafOfModules.toSheaf.{u + 1} _ ≅ _)

/-- **Reading sheaves of `Λ`-modules as sheaves of `Λ̲`-modules preserves small limits.** -/
instance preservesLimitsOfShape_moduleSheafOverConstantCoefficientsFunctor
    (K : Type) [SmallCategory K] :
    PreservesLimitsOfShape K (moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ) := by
  have : PreservesLimitsOfShape K (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
    have : PreservesLimitsOfShape K (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesLimitsOfShape K
        (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
    exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have : PreservesLimitsOfShape K (moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ ⋙
      SheafOfModules.toSheaf.{u + 1} _) :=
    preservesLimitsOfShape_of_natIso
      (moduleSheafOverConstantCoefficientsFunctorCompToSheafIso X Λ).symm
  have : PreservesLimitsOfShape K (SheafOfModules.toSheaf.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, u + 1, u} X Λ).O)) :=
    have := AlgebraicGeometry.SheafOfModules.toSheaf_preservesLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, u + 1, u} X Λ).O)
    have := preservesSmallestLimits_of_preservesLimits (SheafOfModules.toSheaf.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, u + 1, u} X Λ).O))
    inferInstance
  have : ReflectsLimitsOfShape K (SheafOfModules.toSheaf.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, u + 1, u} X Λ).O)) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u + 1} _)

end Comparison

attribute [local instance] AlgebraicGeometry.ProEtale.hasSheafify_proetale_addCommGrpCat_succ
  AlgebraicGeometry.ProEtale.wEqualsLocallyBijective_proetale_addCommGrpCat_succ
attribute [local instance 2000] SheafOfModules.instAbelian

/-- **The completed constant sheaf `Λ̲^∧ = lim (Λ/Iⁿ)̲` on `X_proétale` is derived complete** along
the ideal sheaf `IΛ̲`; this is part (3) of [Stacks, Tag 099Q] on the small pro-étale site. Neither
a Noetherian hypothesis on `Λ` nor finite generation of `I` is needed. -/
theorem isDerivedComplete_completedConstantSheaf_proetale (I : Ideal Λ)
    [HasWeakSheafify (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)] :
    RingedSite.IsDerivedComplete.{u + 1, u, u + 1, u + 1}
      (constantCoefficientRingedSite.{u, u + 1, u} X Λ)
      (constantCoefficientIdealSheaf.{u, u + 1, u} X Λ I)
      ((DerivedCategory.singleFunctor (RingedSite.Modules.{u + 1, u, u + 1}
          (constantCoefficientRingedSite.{u, u + 1, u} X Λ)) 0).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ).obj
          (Stacks.ConstantSheaf.completedConstantSheaf (Scheme.ProEt.topology X) I))) := by
  let Φ := moduleSheafOverConstantCoefficientsFunctor.{u, u + 1, u} X Λ
  let T := Stacks.ConstantSheaf.adicQuotientSheafSystem (Scheme.ProEt.topology X) I
  refine (RingedSite.isDerivedComplete_iff_of_iso _ _
    ((DerivedCategory.singleFunctor _ 0).mapIso (preservesLimitIso Φ T))).2 ?_
  refine isDerivedComplete_limit_proetale X _ _ (T ⋙ Φ) fun n => ?_
  refine RingedSite.isDerivedComplete_single_of_pow_smul_eq_zero_of_slicedObjectsSituation
    (constantCoefficientRingedSite.{u, u + 1, u} X Λ)
    (Scheme.ProEt.slicedObjectsSituation X (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, u + 1, u} X Λ).O)) _ _
    fun U _ f hf => ⟨n, fun x => ?_⟩
  have hf' := pow_mem_annihilatorObj_of_mem_constantCoefficientIdealSheaf X Λ I n (T.obj (op n))
    (fun a ha V s => Stacks.ConstantSheaf.smul_constantSections_eq_zero
      (Scheme.ProEt.topology X) V.unop _ a
      (fun m => Stacks.ConstantSheaf.smul_adicQuotientSystem_obj I n ha m) s) hf
  exact SheafOfModules.smul_eq_zero_of_mem_annihilator _ hf' x

end AlgebraicGeometry.ProEtale

end
