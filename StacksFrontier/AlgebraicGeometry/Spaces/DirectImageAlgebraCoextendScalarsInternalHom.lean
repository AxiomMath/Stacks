module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraExtendScalarsTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraQuasicoherenceCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingAlgebraModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensorComp
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteSheafHomComparisonUlift

/-!
# Coextension of scalars along `π♯ : 𝒪_X ⟶ π_*𝒪_Y` is the internal Hom out of `π_*𝒪_Y`

Let `π : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `𝒜 = π_*𝒪_Y` be the direct-image algebra of Stacks 03G8, and write `E`, `Res`,
`Coext` for extension, restriction and coextension of scalars along `π♯`.  This file identifies

`Res ∘ Coext  ≅  𝓗om_{𝒪_X}(π_*𝒪_Y, -)`

as functors on `𝒪_X`-modules, and reads it at `𝒪_X`: the underlying `𝒪_X`-module of
`𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` carrying its `𝒜`-action is that internal Hom.

That was the one obstruction to quasi-coherence of
`AlgebraicGeometry.Space.dualizingAlgebraModule`, and hence to forming the relative dualizing
module `ω_{Y/X}` of [Stacks, Tag 0GUZ] with the quasi-inverse of the affine direct image
equivalence of [Stacks, Tag 08AI].  Both are below.

## The argument

`E ⊣ Res` is Stacks 03CZ and `Res ⊣ Coext` is the adjunction built in
`StacksFrontier/AlgebraicGeometry/Spaces/DualizingAlgebraModule.lean`, so composing them exhibits
`Coext ⋙ Res` as a right adjoint of `E ⋙ Res`.  The `𝒪_X`-modules also carry the tensor-hom
adjunction `AlgebraicGeometry.RingedSite.sheafTensorRightInternalHomSmallAdjunction` of
Stacks 03EO, whose left half is `- ⊗_{𝒪_X} π_*𝒪_Y` and whose right half is
`𝓗om_{𝒪_X}(π_*𝒪_Y, -)`.  So it suffices to identify the two left adjoints, after which
`CategoryTheory.Adjunction.rightAdjointUniq` identifies the right adjoints; and `E ⋙ Res` *is*
the tensor product by `π_*𝒪_Y`, which is
`AlgebraicGeometry.Space.restrictScalarsExtendScalarsIsoTensorModule`, there proved objectwise.

Three things were missing and are supplied here.

* The objectwise comparison is promoted to an isomorphism of functors.  Its two ingredients are
  natural: `AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso` is the identity
  on sections, so its naturality square holds by `rfl`; and
  `Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend` carries a pure tensor to the
  pure tensor with the same factors, so its naturality square is checked on pure tensors.  The
  universe lift of the sections that `AlgebraicGeometry.Space.tensorModule` carries is dropped,
  the target being the tensor product `Stacks.SheafOfModules.Tensor.sheafTensor` that the
  tensor-hom adjunction is stated for.
* The free rank-one `𝒜`-module read over `𝒪_X` is `π_*𝒪_Y`, that is,
  `AlgebraicGeometry.Space.pushforwardStructureModule`.  This *is* definitional — see
  `AlgebraicGeometry.Space.restrictScalars_unit_structureRingSheafDirectImage` — so the first
  variable of the internal Hom needs no transport, and no functoriality of the internal Hom in
  that variable is needed.
* The tensor product by `π_*𝒪_Y` appears on the left in the comparison and on the right in the
  tensor-hom adjunction.  The `𝒪_X`-modules are symmetric monoidal
  (`AlgebraicGeometry.Space.modulesSymmetricCategory`), and
  `AlgebraicGeometry.Space.modulesTensorObjIso_hom_naturality` identifies the monoidal tensor
  product with `Stacks.SheafOfModules.Tensor.sheafTensor` naturally in each variable, so the
  braiding transports the one to the other.

## Main definitions

* `AlgebraicGeometry.Space.relativeDualizingModule` — the relative dualizing module `ω_{Y/X}`
  of [Stacks, Tag 0GUZ], as the value of the quasi-inverse of [Stacks, Tag 08AI] at
  `AlgebraicGeometry.Space.dualizingAlgebraModule`.

## Main results

* `AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso_hom_naturality` and
  `Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend_hom_naturality` — the two
  naturality squares, and
  `AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationNatIso`,
  `Stacks.NoncommChangeOfRings.Presheaf.tensorObjNatIsoRestrictExtend` — the isomorphisms of
  functors they give.
* `AlgebraicGeometry.Space.restrictScalarsExtendScalarsNatIso` — **naturality of
  `AlgebraicGeometry.Space.restrictScalarsExtendScalarsIsoTensorModule`**: extension of scalars
  along `π♯`, read back over `𝒪_X`, is the tensor product by `π_*𝒪_Y`, as an isomorphism of
  functors.
* `AlgebraicGeometry.Space.restrictScalars_unit_structureRingSheafDirectImage` — restriction of
  scalars along `π♯` carries the free rank-one `π_*𝒪_Y`-module to
  `AlgebraicGeometry.Space.pushforwardStructureModule`.
* `AlgebraicGeometry.Space.restrictCoextendNatIsoInternalHom` — **`Res ∘ Coext` is the internal
  Hom out of `π_*𝒪_Y`.**
* `AlgebraicGeometry.Space.restrictScalars_dualizingAlgebraModuleIso` — the underlying
  `𝒪_X`-module of `AlgebraicGeometry.Space.dualizingAlgebraModule` is
  `AlgebraicGeometry.Space.dualizingPushforward`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_dualizingAlgebraModule` — **the dual of
  `π_*𝒪_Y` is quasi-coherent as an `𝒜`-module**, for an affine `π` whose `π_*𝒪_Y` is of finite
  presentation.
* `AlgebraicGeometry.Space.modulePushforward_relativeDualizingModuleIso` and
  `AlgebraicGeometry.Space.moduleDirectImage_relativeDualizingModuleIso` — the characterising
  isomorphism `π_*ω_{Y/X} ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` of [Stacks, Tag 0GUZ], over `𝒪_X` and over
  `𝒜`.

## Implementation notes

The module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/DualizingAlgebraModule.lean` records the identification
below as missing and says that restriction of scalars of the free rank-one `π_*𝒪_Y`-module is
not definitionally `AlgebraicGeometry.Space.pushforwardStructureModule`.  That last remark is
wrong: it is, and `rfl` proves it inside the default heartbeat budget.

Each isomorphism of functors below is assembled from `CategoryTheory.NatIso.ofComponents` applied
in the direction in which its naturality square is a composite of identities or of images of one
square under a functor, and inverted later, in the places where the other direction is wanted. The
alternative — rewriting inside the naturality square — fails: the same sheaf of rings has three
spellings here (`AlgebraicGeometry.Space.structureRingSheaf`,
`Stacks.SheafOfModules.Tensor.ringSheaf` of the ringed site's structure sheaf, and the ringed
site's own) whose categories of modules are definitionally but not reducibly equal, so `rw` reports
the goal as not type-correct under the `implicit` transparency level.

The two global instances `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and its
Grothendieck counterpart hold only at a module universe which is a `max` of the site universes
and leave a stuck universe constraint at the pinned module universe `u`; they are removed here,
exactly as in `StacksFrontier/AlgebraicGeometry/Spaces/DualizingAlgebraModule.lean`.

Nothing here carries a `stacks` attribute.  The two naturality squares and the identification
of `Res ∘ Coext` are comparisons of constructions; Stacks 03CZ, 03M1 and 03EO are registered
where they are proved; and [Stacks, Tag 0GUZ] asserts more than the isomorphism below — it also
asserts the trace, which is
`AlgebraicGeometry.Space.dualizingTrace`, and the behaviour under base change — so the tag is
registered where that assertion is assembled and not here.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w v₀ r r₀

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type r₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {R R' : Sheaf J RingCat.{r}}

/-- **Restriction of scalars commutes with sheafification naturally.**  The comparison
`AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso` is the identity on sections,
so its naturality square in the presheaf of modules being sheafified holds on the nose. -/
theorem restrictScalarsSheafificationIso_hom_naturality (α : R ⟶ R')
    {P Q : PresheafOfModules.{w} R'.obj} (h : P ⟶ Q) :
    (_root_.SheafOfModules.restrictScalars.{w} α).map
          ((PresheafOfModules.sheafification (R := R') (𝟙 R'.obj)).map h) ≫
        (restrictScalarsSheafificationIso α Q).hom =
      (restrictScalarsSheafificationIso α P).hom ≫
        (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).map
          ((PresheafOfModules.restrictScalars α.hom).map h) := rfl

/-- **Restriction of scalars commutes with sheafification, as an isomorphism of functors.**
Sheafifying a presheaf of `R'`-modules and then restricting the scalars to `R` is restricting
the scalars first and then sheafifying, naturally in the presheaf. -/
def restrictScalarsSheafificationNatIso (α : R ⟶ R') :
    PresheafOfModules.sheafification (R := R') (𝟙 R'.obj) ⋙
        _root_.SheafOfModules.restrictScalars.{w} α ≅
      PresheafOfModules.restrictScalars α.hom ⋙
        PresheafOfModules.sheafification (R := R) (𝟙 R.obj) :=
  NatIso.ofComponents (fun P => restrictScalarsSheafificationIso α P)
    (fun {_ _} h => restrictScalarsSheafificationIso_hom_naturality α h)

end AlgebraicGeometry.SheafOfModules

namespace Stacks.NoncommChangeOfRings.Presheaf

variable {C : Type r₀} [Category.{v₀} C] {R₁ : Cᵒᵖ ⥤ CommRingCat.{r}} {R' : Cᵒᵖ ⥤ RingCat.{r}}
  (α : (R₁ ⋙ forget₂ CommRingCat.{r} RingCat.{r}) ⟶ R')
  (hcomm : ∀ (V : Cᵒᵖ) (a b : R'.obj V), a * b = b * a)

include hcomm in
/-- **The objectwise comparison of the tensor product with the extension of scalars is natural.**
`Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend` carries a pure tensor to the
pure tensor with the same factors, so both sides of its naturality square agree on pure tensors,
and a morphism out of a tensor product is determined by its values there. -/
theorem tensorObjIsoRestrictExtend_hom_naturality
    {M N : PresheafOfModules.{r} (R₁ ⋙ forget₂ CommRingCat.{r} RingCat.{r})} (ψ : M ⟶ N) :
    PresheafOfModules.tensorHom (O := R₁)
          (𝟙 ((PresheafOfModules.restrictScalars α).obj (PresheafOfModules.unit R'))) ψ ≫
        (tensorObjIsoRestrictExtend α hcomm N).hom =
      (tensorObjIsoRestrictExtend α hcomm M).hom ≫
        (PresheafOfModules.restrictScalars α).map ((extendScalars.{r} α).map ψ) :=
  PresheafOfModules.hom_ext fun _ => ModuleCat.MixedTensor.tensor_ext fun _ _ => rfl

include hcomm in
/-- **The objectwise tensor product with `R'`, read as a presheaf of `R₁`-modules, is objectwise
extension of scalars read back along `α`, as an isomorphism of functors.** -/
def tensorObjNatIsoRestrictExtend :
    (PresheafOfModules.tensorBifunctor.{v₀, r₀, r, r, r} R₁).obj
        ((PresheafOfModules.restrictScalars α).obj (PresheafOfModules.unit R')) ≅
      extendScalars.{r} α ⋙ PresheafOfModules.restrictScalars α :=
  NatIso.ofComponents (fun M => tensorObjIsoRestrictExtend α hcomm M)
    (fun {_ _} ψ => tensorObjIsoRestrictExtend_hom_naturality α hcomm ψ)

end Stacks.NoncommChangeOfRings.Presheaf

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The monoidal tensor product as the sheafified objectwise tensor product -/

section Monoidal

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF)

/-- **Tensoring on the left by `M`, as an isomorphism of functors onto the sheafified objectwise
tensor product.**  `AlgebraicGeometry.Space.modulesTensorObjIso` objectwise, whose naturality is
`AlgebraicGeometry.Space.modulesTensorObjIso_hom_naturality` with the identity of `M` in the
first variable. -/
def modulesTensorLeftNatIso :
    tensorLeft M ≅ (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS F hF)).obj M :=
  NatIso.ofComponents (fun N => modulesTensorObjIso B S hS F hF M N) (fun {N N'} b => by
    have cancel : ∀ {A₁ A₂ C₁ C₂ : Modules.{u, u} B S hS F hF} {p : A₁ ⟶ A₂} {t : C₁ ⟶ C₂}
        {e₁ : A₁ ≅ C₁} {e₂ : A₂ ≅ C₂} {x : C₁ ⟶ C₁},
        x = 𝟙 C₁ → p ≫ e₂.hom = e₁.hom ≫ x ≫ t → p ≫ e₂.hom = e₁.hom ≫ t := by
      intro _ _ _ _ _ _ _ _ _ hx hh
      rw [hx, Category.id_comp] at hh
      exact hh
    refine (congrArg (fun k => k ≫ (modulesTensorObjIso B S hS F hF M N').hom)
      (MonoidalCategory.id_tensorHom M b).symm).trans ?_
    refine cancel ?_ (modulesTensorObjIso_hom_naturality B S hS (𝟙 M) b)
    exact NatTrans.congr_app (CategoryTheory.Functor.map_id _ M) N)

/-- **Tensoring on the right by `M`, as an isomorphism of functors onto the sheafified objectwise
tensor product.**  `AlgebraicGeometry.Space.modulesTensorObjIso` objectwise, whose naturality is
`AlgebraicGeometry.Space.modulesTensorObjIso_hom_naturality` with the identity of `M` in the
second variable. -/
def modulesTensorRightNatIso :
    tensorRight M ≅ (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS F hF)).flip.obj M :=
  NatIso.ofComponents (fun N => modulesTensorObjIso B S hS F hF N M) (fun {N N'} a => by
    have cancel : ∀ {A₁ A₂ C₁ C₂ : Modules.{u, u} B S hS F hF} {p : A₁ ⟶ A₂} {t : C₁ ⟶ C₂}
        {e₁ : A₁ ≅ C₁} {e₂ : A₂ ≅ C₂} {x : C₂ ⟶ C₂},
        x = 𝟙 C₂ → p ≫ e₂.hom = e₁.hom ≫ t ≫ x → p ≫ e₂.hom = e₁.hom ≫ t := by
      intro _ _ _ _ _ _ _ _ _ hx hh
      rw [hx, Category.comp_id] at hh
      exact hh
    refine (congrArg (fun k => k ≫ (modulesTensorObjIso B S hS F hF N' M).hom)
      (MonoidalCategory.tensorHom_id a M).symm).trans ?_
    refine cancel ?_ (modulesTensorObjIso_hom_naturality B S hS a (𝟙 M))
    exact CategoryTheory.Functor.map_id _ M)

/-- **The braiding, as an isomorphism between the two sheafified objectwise tensor products by
`M`.**  `M ⊗ -` and `- ⊗ M` are isomorphic because the `𝒪_F`-modules are symmetric monoidal;
this transports that isomorphism to the shape `Stacks.SheafOfModules.Tensor.sheafTensor` in
which the tensor-hom adjunction of Stacks 03EO is stated. -/
def sheafTensorBraidingNatIso :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS F hF)).obj M ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS F hF)).flip.obj M :=
  (modulesTensorLeftNatIso B S hS F hF M).symm ≪≫
    BraidedCategory.tensorLeftIsoTensorRight M ≪≫ modulesTensorRightNatIso B S hS F hF M

end Monoidal

/-! ### Extension of scalars along `π♯`, read back over `𝒪_X`, is the tensor product -/

variable {Y X : AlgebraicSpaces B S hS}

/-- **The free rank-one `π_*𝒪_Y`-module, read as an `𝒪_X`-module along `π♯`, is `π_*𝒪_Y`.**

Equivalently, the direct image of `𝒪_Y`-modules of Stacks 03D1 carries `𝒪_Y` to the free
rank-one module over `𝒜 = π_*𝒪_Y`.  The two readings of the direct image differ only by
restriction of scalars along `π♯`
(`AlgebraicGeometry.Space.restrictScalars_moduleDirectImage`), and the inverse image of a sheaf
of rings is built from the same sections as the inverse image of the free module of rank one
over it, so the identity holds on the nose. -/
theorem restrictScalars_unit_structureRingSheafDirectImage (π : Y ⟶ X) :
    (directImageAlgebraRestrictScalars B S hS π).obj
        (SheafOfModules.unit (structureRingSheafDirectImage B S hS π)) =
      pushforwardStructureModule B S hS π := rfl

/-- The factorisation of extension of scalars along `π♯` read back over `𝒪_X` through presheaves
of modules: forget the sheaf condition, extend the scalars objectwise, read the result back over
`𝒪_X`, and sheafify.  Both
`AlgebraicGeometry.Space.directImageAlgebraExtendScalars ⋙
AlgebraicGeometry.Space.directImageAlgebraRestrictScalars` and the tensor product by `π_*𝒪_Y`
are compared with it. -/
def extendRestrictPresheafFactorisation (π : Y ⟶ X) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  SheafOfModules.forget.{u} (structureRingSheaf B S hS X) ⋙
    Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u} (structureSharp B S hS π).hom ⋙
      PresheafOfModules.restrictScalars (structureSharp B S hS π).hom ⋙
        PresheafOfModules.sheafification.{u} (R := structureRingSheaf B S hS X)
          (𝟙 (structureRingSheaf B S hS X).obj)

/-- Extension of scalars along `π♯`, read back over `𝒪_X`, factors through
`AlgebraicGeometry.Space.extendRestrictPresheafFactorisation`: restriction of scalars commutes
with sheafification. -/
def extendRestrictNatIsoFactorisation (π : Y ⟶ X) :
    directImageAlgebraExtendScalars B S hS π ⋙ directImageAlgebraRestrictScalars B S hS π ≅
      extendRestrictPresheafFactorisation B S hS π :=
  NatIso.ofComponents
    (fun G =>
      AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso.{u, u, u, u + 1}
        (structureSharp B S hS π)
        ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u}
          (structureSharp B S hS π).hom).obj G.val))
    (fun {_ _} g =>
      AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso_hom_naturality
        (structureSharp B S hS π)
        ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u}
          (structureSharp B S hS π).hom).map g.val))

/-- The naturality square of `AlgebraicGeometry.Space.tensorNatIsoFactorisation`, kept as a
declaration of its own and stated for the free rank-one `π_*𝒪_Y`-module read over `𝒪_X` rather
than for `AlgebraicGeometry.Space.pushforwardStructureModule`: the two agree by
`AlgebraicGeometry.Space.restrictScalars_unit_structureRingSheafDirectImage`, but only by an
expensive definitional unfolding, while the underlying presheaf of the former is visibly the
restriction of scalars of the free presheaf of modules that
`Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend` starts from.  The tensor
product sheaf on a morphism is first read as the sheafified objectwise tensor product by
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_map`, and the square is then the image under
sheafification of
`Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend_hom_naturality`. -/
theorem tensorNatIsoFactorisation_naturality (π : Y ⟶ X)
    {G G' : Modules.{u, u} B S hS X.1 X.2} (g : G ⟶ G') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS X.1 X.2)).obj
          ((directImageAlgebraRestrictScalars B S hS π).obj
            (SheafOfModules.unit (structureRingSheafDirectImage B S hS π)))).map g ≫
        ((PresheafOfModules.sheafification.{u} (R := structureRingSheaf B S hS X)
          (𝟙 (structureRingSheaf B S hS X).obj)).mapIso
          (Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend
            (R₁ := (smallEtaleRingedSite B S hS X.1 X.2).O.obj)
            (structureSharp B S hS π).hom
            (mul_comm_structureRingSheafDirectImage B S hS π) G'.val)).hom =
      ((PresheafOfModules.sheafification.{u} (R := structureRingSheaf B S hS X)
          (𝟙 (structureRingSheaf B S hS X).obj)).mapIso
          (Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend
            (R₁ := (smallEtaleRingedSite B S hS X.1 X.2).O.obj)
            (structureSharp B S hS π).hom
            (mul_comm_structureRingSheafDirectImage B S hS π) G.val)).hom ≫
        (extendRestrictPresheafFactorisation B S hS π).map g := by
  refine (congrArg (· ≫ _)
    (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map _ _ g)).trans ?_
  exact (((PresheafOfModules.sheafification.{u} (R := structureRingSheaf B S hS X)
        (𝟙 (structureRingSheaf B S hS X).obj)).map_comp _ _).symm.trans
    (congrArg (PresheafOfModules.sheafification.{u} (R := structureRingSheaf B S hS X)
        (𝟙 (structureRingSheaf B S hS X).obj)).map
      (Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend_hom_naturality
        (R₁ := (smallEtaleRingedSite B S hS X.1 X.2).O.obj)
        (structureSharp B S hS π).hom
        (mul_comm_structureRingSheafDirectImage B S hS π) g.val))).trans
    ((PresheafOfModules.sheafification.{u} (R := structureRingSheaf B S hS X)
        (𝟙 (structureRingSheaf B S hS X).obj)).map_comp _ _)

/-- The tensor product by `π_*𝒪_Y` factors through
`AlgebraicGeometry.Space.extendRestrictPresheafFactorisation`: before sheafifying, the
objectwise tensor product with `𝒜` is the objectwise extension of scalars read back over
`𝒪_X`.  The module `π_*𝒪_Y` is first replaced by the free rank-one `𝒜`-module read over `𝒪_X`
along the equation `AlgebraicGeometry.Space.restrictScalars_unit_structureRingSheafDirectImage`,
so that no definitional unfolding of `AlgebraicGeometry.Space.pushforwardStructureModule` is
needed. -/
def tensorNatIsoFactorisation (π : Y ⟶ X) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS X.1 X.2)).obj (pushforwardStructureModule B S hS π) ≅
      extendRestrictPresheafFactorisation B S hS π :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS X.1 X.2)).mapIso
      (eqToIso (restrictScalars_unit_structureRingSheafDirectImage B S hS π).symm) ≪≫
    NatIso.ofComponents
      (fun G =>
        (PresheafOfModules.sheafification.{u} (R := structureRingSheaf B S hS X)
            (𝟙 (structureRingSheaf B S hS X).obj)).mapIso
          (Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend
            (R₁ := (smallEtaleRingedSite B S hS X.1 X.2).O.obj)
            (structureSharp B S hS π).hom
            (mul_comm_structureRingSheafDirectImage B S hS π) G.val))
      (fun {_ _} g => tensorNatIsoFactorisation_naturality B S hS π g)

/-- **Naturality of `AlgebraicGeometry.Space.restrictScalarsExtendScalarsIsoTensorModule`.**
Extension of scalars along `π♯ : 𝒪_X ⟶ 𝒜`, read back as a functor to `𝒪_X`-modules, is the
tensor product by `𝒜 = π_*𝒪_Y`, as an isomorphism of *functors*.

The target is `Stacks.SheafOfModules.Tensor.sheafTensor`, the shape of the tensor product the
tensor-hom adjunction of Stacks 03EO is stated for, rather than
`AlgebraicGeometry.Space.tensorModule`, which raises the universe of the sections by a universe
they already lie in. -/
def restrictScalarsExtendScalarsNatIso (π : Y ⟶ X) :
    directImageAlgebraExtendScalars B S hS π ⋙ directImageAlgebraRestrictScalars B S hS π ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS X.1 X.2)).obj (pushforwardStructureModule B S hS π) :=
  extendRestrictNatIsoFactorisation B S hS π ≪≫ (tensorNatIsoFactorisation B S hS π).symm

/-- **Extension of scalars along `π♯`, read back over `𝒪_X`, is tensoring on the right by
`π_*𝒪_Y`** — the left half of the tensor-hom adjunction of Stacks 03EO.

This is `AlgebraicGeometry.Space.restrictScalarsExtendScalarsNatIso` followed by the braiding of
`AlgebraicGeometry.Space.sheafTensorBraidingNatIso`. -/
def restrictScalarsExtendScalarsNatIsoTensorRight (π : Y ⟶ X) :
    directImageAlgebraExtendScalars B S hS π ⋙ directImageAlgebraRestrictScalars B S hS π ≅
      RingedSite.tensorRightModules (smallEtaleRingedSite B S hS X.1 X.2)
        (pushforwardStructureModule B S hS π) :=
  restrictScalarsExtendScalarsNatIso B S hS π ≪≫
    sheafTensorBraidingNatIso B S hS X.1 X.2 (pushforwardStructureModule B S hS π)

/-! ### Coextension of scalars is the internal Hom -/

/-- **Coextension of scalars along `π♯ : 𝒪_X ⟶ 𝒜`, read back over `𝒪_X`, is the internal Hom out
of `π_*𝒪_Y`.**

`E ⊣ Res` (Stacks 03CZ) composed with `Res ⊣ Coext` exhibits `Coext ⋙ Res` as a right adjoint of
`E ⋙ Res`, which is `- ⊗_{𝒪_X} π_*𝒪_Y` by
`AlgebraicGeometry.Space.restrictScalarsExtendScalarsNatIsoTensorRight`; the internal Hom out of
`π_*𝒪_Y` is a right adjoint of the same functor by Stacks 03EO
(`AlgebraicGeometry.RingedSite.sheafTensorRightInternalHomSmallAdjunction`), and a right adjoint
is unique. -/
def restrictCoextendNatIsoInternalHom (π : Y ⟶ X) :
    directImageAlgebraCoextendScalars B S hS π ⋙ directImageAlgebraRestrictScalars B S hS π ≅
      RingedSite.internalHomSheafSmallFunctor.{u} (smallEtaleRingedSite B S hS X.1 X.2)
        (pushforwardStructureModule B S hS π) :=
  Adjunction.rightAdjointUniq
    (((directImageAlgebraExtendRestrictAdjunction B S hS π).comp
          (directImageAlgebraRestrictCoextendAdjunction B S hS π)).ofNatIsoLeft
      (restrictScalarsExtendScalarsNatIsoTensorRight B S hS π))
    (RingedSite.sheafTensorRightInternalHomSmallAdjunction
      (smallEtaleRingedSite B S hS X.1 X.2) (pushforwardStructureModule B S hS π))

/-- **The underlying `𝒪_X`-module of `AlgebraicGeometry.Space.dualizingAlgebraModule` is
`AlgebraicGeometry.Space.dualizingPushforward`**: forgetting the `π_*𝒪_Y`-action on
`𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` gives that internal Hom.

This is the identification that the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/DualizingAlgebraModule.lean` records as missing. -/
def restrictScalars_dualizingAlgebraModuleIso (π : Y ⟶ X) :
    (directImageAlgebraRestrictScalars B S hS π).obj (dualizingAlgebraModule B S hS π) ≅
      dualizingPushforward B S hS π :=
  (restrictCoextendNatIsoInternalHom B S hS π).app
    (SheafOfModules.unit (structureRingSheaf B S hS X))

/-! ### Quasi-coherence, and the relative dualizing module -/

/-- **The dual `𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` is quasi-coherent as a `π_*𝒪_Y`-module**, for an affine
morphism of algebraic spaces whose `π_*𝒪_Y` is of finite presentation.

Its underlying `𝒪_X`-module is `AlgebraicGeometry.Space.dualizingPushforward`, which is
quasi-coherent by Stacks 03M1(6), and the second assertion of Stacks 08AI turns quasi-coherence
over `𝒪_X` into quasi-coherence over `π_*𝒪_Y`. -/
theorem isQuasicoherentOnSite_dualizingAlgebraModule (π : Y ⟶ X)
    (hπ : IsAffineHom B S hS π.hom)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite) :
    (dualizingAlgebraModule B S hS π).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_restrictScalars_structureSharp_iff B S hS π hπ
      (dualizingAlgebraModule B S hS π)).1
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      (restrictScalars_dualizingAlgebraModuleIso B S hS π).symm
      (isQuasicoherentOnSite_dualizingPushforward B S hS π
        (isQuasicoherentOnSite_restrictScalars_structureRingSheafDirectImage B S hS π hπ) hfp))

/-- **The relative dualizing module `ω_{Y/X}` of a morphism of algebraic spaces**, as
[Stacks, Tag 0GUZ] constructs it: the quasi-inverse of the affine direct image equivalence of
[Stacks, Tag 08AI] applied to the dual `𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` with its `π_*𝒪_Y`-action.

The construction itself needs no hypothesis on `π`; it is the characterising isomorphism
`π_*ω_{Y/X} ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` that does, through the invertibility of the unit of
Stacks 03D4 at a quasi-coherent module. -/
def relativeDualizingModule (π : Y ⟶ X) : Modules.{u, u} B S hS Y.1 Y.2 :=
  (directImageAlgebraPullback B S hS π).obj (dualizingAlgebraModule B S hS π)

/-- **The relative dualizing module is quasi-coherent**, for an affine morphism of algebraic
spaces whose `π_*𝒪_Y` is of finite presentation: the quasi-inverse of Stacks 08AI carries
quasi-coherent `π_*𝒪_Y`-modules to quasi-coherent `𝒪_Y`-modules. -/
theorem isQuasicoherentOnSite_relativeDualizingModule (π : Y ⟶ X)
    (hπ : IsAffineHom B S hS π.hom)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite) :
    (relativeDualizingModule B S hS π).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_directImageAlgebraPullback B S hS π hπ _
    (isQuasicoherentOnSite_dualizingAlgebraModule B S hS π hπ hfp)

/-- **The characterising isomorphism of [Stacks, Tag 0GUZ], over `𝒜 = π_*𝒪_Y`:**
`π_*ω_{Y/X} ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` as `π_*𝒪_Y`-modules.

It is the unit of Stacks 03D4 at `AlgebraicGeometry.Space.dualizingAlgebraModule`, invertible
because that module is quasi-coherent and `π` is affine. -/
def moduleDirectImage_relativeDualizingModuleIso (π : Y ⟶ X)
    (hπ : IsAffineHom B S hS π.hom)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite) :
    dualizingAlgebraModule B S hS π ≅
      (moduleDirectImage B S hS π).obj (relativeDualizingModule B S hS π) :=
  @asIso _ _ _ _
    ((directImageAlgebraPullbackAdjunction B S hS π).unit.app
      (dualizingAlgebraModule B S hS π))
    (isIso_directImageAlgebraPullbackAdjunction_unit_app_of_isAffineHom B S hS π hπ
      (dualizingAlgebraModule B S hS π)
      (isQuasicoherentOnSite_dualizingAlgebraModule B S hS π hπ hfp))

/-- **The characterising isomorphism of [Stacks, Tag 0GUZ], over `𝒪_X`:**
`π_*ω_{Y/X} ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` as `𝒪_X`-modules, with the direct image of Stacks 03LU on
the left.

It is `AlgebraicGeometry.Space.moduleDirectImage_relativeDualizingModuleIso` read over `𝒪_X` —
the two readings of the direct image differ only by restriction of scalars along `π♯` — followed
by `AlgebraicGeometry.Space.restrictScalars_dualizingAlgebraModuleIso`. -/
def modulePushforward_relativeDualizingModuleIso (π : Y ⟶ X)
    (hπ : IsAffineHom B S hS π.hom)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite) :
    (modulePushforward B S hS π).obj (relativeDualizingModule B S hS π) ≅
      dualizingPushforward B S hS π :=
  ((directImageAlgebraRestrictScalars B S hS π).mapIso
      (moduleDirectImage_relativeDualizingModuleIso B S hS π hπ hfp)).symm ≪≫
    restrictScalars_dualizingAlgebraModuleIso B S hS π

end AlgebraicGeometry.Space

end
