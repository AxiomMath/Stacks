module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialSurjectivity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFullyFaithful.PullbackModuleFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposLowerShriekUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback

/-!
# Descent of sheaves of modules along a morphism of ringed topoi with invertible structure map

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi whose structure map in
inverse-image form `f♯ : f⁻¹O_D ⟶ O_C` is an isomorphism. The pullback of sheaves of modules
`f^* = O_C ⊗_{f⁻¹O_D} f⁻¹(-)` of Stacks 03D6 then performs no genuine extension of scalars, and
this file transfers full faithfulness and the description of the essential image from the
underlying morphism of topoi to sheaves of modules:

* if `f⁻¹` is fully faithful on sheaves of sets then `f^*` is fully faithful on sheaves of
  modules;
* a sheaf of `O_C`-modules whose underlying sheaf of sets lies in the essential image of `f⁻¹`
  lies in the essential image of `f^*`.

Together these say that `f^*` is an equivalence onto the full subcategory of those sheaves of
modules whose underlying sheaf of sets descends, with `f_*` as quasi-inverse.

## Main results

* `Stacks.Sheaves.RingedToposModules.essImage_inverseImageModules_of_essImage_moduleSheaf`: a
  sheaf of modules over the inverse-image sheaf of rings whose underlying sheaf of sets is an
  inverse image is itself an inverse image, for the Stacks 03D2 inverse image of modules along a
  morphism of topoi with fully faithful inverse image.
* `AlgebraicGeometry.RingedToposHom.isEquivalence_extendScalarsFSharp`: extension of scalars
  along an invertible structure map is an equivalence.
* `AlgebraicGeometry.RingedToposHom.full_pullbackModules`,
  `.faithful_pullbackModules` and `.fullyFaithfulPullbackModules`: the pullback of sheaves of
  modules along a morphism of ringed topoi with invertible structure map is fully faithful as
  soon as the inverse image on sheaves of sets is.
* `AlgebraicGeometry.RingedToposHom.essImage_pullbackModules_of_essImage_moduleSheaf`: the
  essential-image statement for that pullback.

## Implementation notes

Both halves are reductions along the factorization of the pullback of modules into its two
factors: the Stacks 03D2 inverse image of modules, which is transport along `f⁻¹` and therefore
inherits full faithfulness from it by
`Stacks.Sheaves.ToposPullback.fullyFaithfulPullbackModuleFunctor`, and extension of scalars along
the structure map, which for an invertible structure map is restriction of scalars along the
inverse and hence an equivalence. Fullness and faithfulness compose; for the essential image the
second factor being an equivalence lets the question be moved to the first factor by restricting
scalars along the structure map, which leaves the underlying sheaf of sets untouched.

The essential-image statement for the first factor is the counit of the Stacks 03D3 adjunction
read on underlying sheaves of sets: by
`moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit_app`
that counit *is* the counit of `f⁻¹ ⊣ f_*` at the underlying sheaf, so it is invertible exactly
when the underlying sheaf lies in the essential image of the fully faithful `f⁻¹`
(`CategoryTheory.Adjunction.isIso_counit_app_iff_mem_essImage`), and a morphism of sheaves of
modules whose underlying morphism of sheaves of sets is invertible is invertible
(`Stacks.Sheaves.PushforwardEssentialImage.isIso_of_isIso_moduleSheafFunctor_map`). This is the
mirror image, for the left adjoint, of the argument that
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardEssentialSurjectivity.lean` runs for the
right adjoint.

No surjectivity or local surjectivity of the structure map is used, and no condition on the
topoi beyond the standing existence hypotheses for the underlying-sheaf functors; in particular
nothing here is special to a closed immersion.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.PushforwardEssentialImage

namespace Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'})

/-- **A sheaf of modules over the inverse-image sheaf of rings whose underlying sheaf of sets is
an inverse image is itself an inverse image.** For a morphism of topoi whose inverse image on
sheaves of sets is fully faithful, the Stacks 03D2 inverse image of sheaves of modules
`Mod(O) ⥤ Mod(f⁻¹O)` has in its essential image every sheaf of `f⁻¹O`-modules whose underlying
sheaf of sets lies in the essential image of `f⁻¹`.

The witness is the counit of the Stacks 03D3 adjunction at the module, which on underlying
sheaves of sets is the counit of `f⁻¹ ⊣ f_*` at its underlying sheaf; that one is invertible
because a fully faithful left adjoint has invertible counit exactly on its essential image, and
invertibility transfers back because the underlying sheaf of sets detects isomorphisms of sheaves
of modules. -/
theorem essImage_inverseImageModules_of_essImage_moduleSheaf
    [f.inverseImage.Full] [f.inverseImage.Faithful]
    (M : SheafOfModules.{w} (inverseImageRingSheaf f O))
    (h : f.inverseImage.essImage (Sheaf.moduleSheaf (inverseImageRingSheaf f O) M)) :
    (inverseImageModules f O).essImage M := by
  have hc : IsIso (f.adj.counit.app (Sheaf.moduleSheaf (inverseImageRingSheaf f O) M)) :=
    (f.adj.isIso_counit_app_iff_mem_essImage).mpr h
  have hm : IsIso ((inverseImageAdjDirectImageModules f O).counit.app M) := by
    refine isIso_of_isIso_moduleSheafFunctor_map _ ?_
    rw [moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit_app]
    exact hc
  exact ⟨_, ⟨@asIso _ _ _ _ ((inverseImageAdjDirectImageModules f O).counit.app M) hm⟩⟩

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

open Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [Y.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- **Extension of scalars along an invertible structure map is an equivalence.** It is
isomorphic to restriction of scalars along the inverse of the structure map, which is an
equivalence of the categories of sheaves of modules. -/
theorem isEquivalence_extendScalarsFSharp :
    Functor.IsEquivalence (extendScalarsFSharp f.toModulesHom) :=
  have := (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (asIso f.toModulesHom.fSharpInverseImage)).isEquivalence_functor
  Functor.isEquivalence_of_iso
    (RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso f.toModulesHom).symm

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [IsIso f.fSharpInverseImage] in
/-- The pullback of sheaves of modules along a morphism of ringed topoi is the Stacks 03D2
inverse image of modules followed by extension of scalars along the structure map. -/
theorem pullbackModules_eq :
    f.toModulesHom.pullbackModules =
      inverseImageModules f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) ⋙
        extendScalarsFSharp f.toModulesHom :=
  rfl

/-- **The pullback of sheaves of modules along a morphism of ringed topoi with invertible
structure map is faithful as soon as the inverse image on sheaves of sets is.** -/
theorem faithful_pullbackModules [f.toToposHom.inverseImage.Faithful] :
    f.toModulesHom.pullbackModules.Faithful := by
  have hequiv := (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (asIso f.toModulesHom.fSharpInverseImage)).isEquivalence_functor
  have hext : (extendScalarsFSharp f.toModulesHom).Faithful :=
    Functor.Faithful.of_iso
      (RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso f.toModulesHom).symm
  have hinv : (inverseImageModules f.toToposHom
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).Faithful :=
    inferInstance
  rw [pullbackModules_eq f]
  exact @Functor.Faithful.comp _ _ _ _ _ _ _ _ hinv hext

/-- **The pullback of sheaves of modules along a morphism of ringed topoi with invertible
structure map is full as soon as the inverse image on sheaves of sets is fully faithful.**

The pullback is the Stacks 03D2 inverse image of modules followed by extension of scalars along
the structure map. The first factor is transport of sheaves of modules along `f⁻¹` and is full by
`Stacks.Sheaves.ToposPullback.full_pullbackModuleFunctor`; the second is an equivalence. -/
theorem full_pullbackModules
    [f.toToposHom.inverseImage.Full] [f.toToposHom.inverseImage.Faithful] :
    f.toModulesHom.pullbackModules.Full := by
  have hequiv := (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (asIso f.toModulesHom.fSharpInverseImage)).isEquivalence_functor
  have hext : (extendScalarsFSharp f.toModulesHom).Full :=
    Functor.Full.of_iso
      (RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso f.toModulesHom).symm
  have hinv : (inverseImageModules f.toToposHom
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).Full :=
    inferInstance
  rw [pullbackModules_eq f]
  exact @Functor.Full.comp _ _ _ _ _ _ _ _ hinv hext

/-- **The pullback of sheaves of modules along a morphism of ringed topoi with invertible
structure map is fully faithful as soon as the inverse image on sheaves of sets is.** -/
def fullyFaithfulPullbackModules
    [f.toToposHom.inverseImage.Full] [f.toToposHom.inverseImage.Faithful] :
    f.toModulesHom.pullbackModules.FullyFaithful :=
  haveI := full_pullbackModules f
  haveI := faithful_pullbackModules f
  Functor.FullyFaithful.ofFullyFaithful _

/-- **A sheaf of `O_C`-modules whose underlying sheaf of sets is an inverse image is a
pullback.** For a morphism of ringed topoi with invertible structure map whose inverse image on
sheaves of sets is fully faithful, a sheaf of `O_C`-modules lies in the essential image of
`f^* : Mod(O_D) ⥤ Mod(O_C)` as soon as its underlying sheaf of sets lies in the essential image
of `f⁻¹`.

Restricting scalars along the structure map moves the question to the Stacks 03D2 inverse image
of modules without changing the underlying sheaf of sets, where it is
`Stacks.Sheaves.RingedToposModules.essImage_inverseImageModules_of_essImage_moduleSheaf`;
extension of scalars is an equivalence, so the restricted module is carried back to the given
one. -/
theorem essImage_pullbackModules_of_essImage_moduleSheaf
    [f.toToposHom.inverseImage.Full] [f.toToposHom.inverseImage.Faithful]
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
    (hM : f.toToposHom.inverseImage.essImage
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M)) :
    f.toModulesHom.pullbackModules.essImage M := by
  set E := Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (asIso f.toModulesHom.fSharpInverseImage) with hE
  obtain ⟨N, ⟨e⟩⟩ := essImage_inverseImageModules_of_essImage_moduleSheaf f.toToposHom
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) (E.inverse.obj M) hM
  refine ⟨N, ⟨?_⟩⟩
  refine Iso.trans ?_ (E.counitIso.app M)
  exact (RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso f.toModulesHom).app _ ≪≫
    E.functor.mapIso e

end AlgebraicGeometry.RingedToposHom

end
