module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalenceNatural

/-!
# Internal Hom along a functor of ringed sites which is an equivalence on every slice

Let `(C, O_C)` and `(D, O_D)` be ringed sites and let `Φ : C ⥤ D` be a continuous functor
together with a structure map `φ : O_C ⟶ Φ_* O_D`, such that for every object `W` of `C` the
pushforward of sheaves of modules along the slice functor `Over.post Φ : C/W ⥤ D/Φ(W)`, with the
structure map `φ` whiskered along the slice projection, is fully faithful. This is the situation
of étale localization: for an étale morphism `u : U ⟶ X` of algebraic spaces, postcomposition with
`u` is such a functor between the small étale sites (Stacks 04M0), and the pushforward along it is
the restriction `u^*` of modules. The transport of the internal Hom complex is then the internal
Hom complex of the transports, and so is the transport of the derived internal Hom:

```
φ_* SheafHom^•(A, B) ≅ SheafHom^•(φ_* A, φ_* B),
φ_* RSheafHom(K, L) ≅ RSheafHom(φ_* K, φ_* L).
```

For an equivalence of sites this is `AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso`
and `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomNatIso`, and the proofs are those, with
the equivalence of slices induced by an equivalence of sites replaced by the slice functor of `Φ`:
nothing in them uses more than the full faithfulness of the pushforward of modules along the
slice functor. In the derived statement the transport of a K-injective complex has to stay
K-injective, which for an equivalence is Stacks 08BJ applied to its inverse; here it is a
hypothesis, discharged in the étale case by the exact left adjoint `u_!` of `u^*`.

## Main definitions

* `AlgebraicGeometry.RingedSite.postSlicePhi`: the structure map localized at an object `W`.
* `AlgebraicGeometry.RingedSite.postSliceSheafHomComplexIso`: **the chain-level transport.**
* `AlgebraicGeometry.RingedSite.postSliceDerivedSheafHomNatIso`: **the derived-level transport**,
  natural in both variables and pinned on K-injective models.

## Main results

* `AlgebraicGeometry.RingedSite.postSliceSectionIso_apply`: on a local homogeneous cochain the
  chain-level transport is the pushforward along the slice functor.
* `AlgebraicGeometry.RingedSite.postSliceSheafHomComplexIso_natural`: the chain-level transport is
  natural in both variables.
* `AlgebraicGeometry.RingedSite.postSliceDerivedSheafHomNatIso_model`,
  `postSliceDerivedSheafHomNatIso_natural_left`, `postSliceDerivedSheafHomNatIso_natural_right`.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {X Y : RingedSite.{u, u, u}} (Φ : Y.C ⥤ X.C) [Φ.IsContinuous Y.J X.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (Φ.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The slice functor of a continuous functor is continuous for the localized topologies. -/
instance postSlice_isContinuous (W : Y.C) :
    (Over.post (X := W) Φ).IsContinuous (Y.J.over W) (X.J.over (Φ.obj W)) :=
  Functor.isContinuous_overPost Y.J X.J Φ W

/-- The structure map `O_C ⟶ Φ_* O_D` localized at an object `W` of `C`: `φ` whiskered along the
slice projection, which is possible because restricting along the slice functor
`C/W ⥤ D/Φ(W)` and then along `Over.forget` is restricting along `Over.forget` and then
along `Φ`. -/
def postSlicePhi (W : Y.C) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) ⟶
      ((Over.post (X := W) Φ).sheafPushforwardContinuous RingCat.{u}
        (Y.J.over W) (X.J.over (Φ.obj W))).obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (Φ.obj W)) :=
  ⟨Functor.whiskerLeft (Over.forget W).op φ.hom⟩

/-- Transport of sheaves of modules on the slice over `Φ(W)` to the slice over `W`, along the
slice functor. -/
abbrev postSliceFunctor (W : Y.C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (Φ.obj W)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  SheafOfModules.pushforward.{u} (postSlicePhi Φ φ W)

/-- Transport of complexes of modules along `φ`. -/
abbrev postSlicePushComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ :=
  (SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)

variable (hff : ∀ W : Y.C, (postSliceFunctor Φ φ W).FullyFaithful)

/-- The transport of sheaves of modules along the slice functor is additive. -/
instance postSliceFunctor_additive (W : Y.C) : (postSliceFunctor Φ φ W).Additive where
  map_add := by intros; rfl

section

variable (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

include hff in
/-- The complex of sections over `W` of the transported internal Hom complex is the internal Hom
complex of the transports: the sections of the transport over `W` are the sections over `Φ(W)`,
which are the cochains on the slice over `Φ(W)`, and the slice functor carries those to the
cochains on the slice over `W`. -/
def postSliceSectionIso (W : Y.C) :
    sectionComplex X (sheafHomComplex X A B).obj (Φ.obj W) ≅
      sectionComplex Y (sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
        ((postSlicePushComplex Φ φ).obj B)).obj W :=
  haveI := (hff W).full
  haveI := (hff W).faithful
  (sheafHomComplex X A B).sectionsIso (Φ.obj W) ≪≫
    homComplexMapIso (postSliceFunctor Φ φ W) _ _ ≪≫
    ((sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
      ((postSlicePushComplex Φ φ).obj B)).sectionsIso W).symm

/-- On cochains, `postSliceSectionIso` transports each local homogeneous component along the
slice functor. -/
theorem postSliceSectionIso_apply (W : Y.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op (Φ.obj W))) :
    (AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
        ((postSlicePushComplex Φ φ).obj B)).sectionsIso W).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((postSliceSectionIso Φ φ hff A B W).hom.f n) s)).v p q hpq =
    (postSliceFunctor Φ φ W).map
      ((AddCommGrpCat.Hom.hom
        (((sheafHomComplex X A B).sectionsIso (Φ.obj W)).hom.f n) s).v p q hpq) := by
  have := (hff W).full
  have := (hff W).faithful
  have h := Iso.inv_hom_id_apply
    ((HomologicalComplex.eval _ _ n).mapIso
      ((sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
        ((postSlicePushComplex Φ φ).obj B)).sectionsIso W))
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X A B).sectionsIso (Φ.obj W)).hom.f n) s).map
        (postSliceFunctor Φ φ W))
  exact congrArg (fun z => z.v p q hpq) h

/-- `postSliceSectionIso` evaluated on a section of the source complex over a slice object: the
local homogeneous component is the one of the original cochain, read at the image slice
object. -/
theorem postSliceSectionIso_apply_section (W : Y.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op (Φ.obj W)))
    {Z : Y.C} (g : Z ⟶ W)
    (x : ((((postSlicePushComplex Φ φ).obj A).X p).val.obj (op Z))) :
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
        ((postSlicePushComplex Φ φ).obj B)).sectionsIso W).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((postSliceSectionIso Φ φ hff A B W).hom.f n) s)).v p q hpq).val.app
          (op (Over.mk g)) x =
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X A B).sectionsIso (Φ.obj W)).hom.f n) s).v
        p q hpq).val.app (op (Over.mk (Φ.map g))) x := by
  rw [postSliceSectionIso_apply]
  rfl

/-- `postSliceSectionIso_apply_section` with the slice object on the target site presented by any
morphism equal to the image of `g`. -/
theorem postSliceSectionIso_apply_section_of_eq (W : Y.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op (Φ.obj W)))
    {Z : Y.C} (g : Z ⟶ W) (m : Φ.obj Z ⟶ Φ.obj W) (hm : m = Φ.map g)
    (x : ((((postSlicePushComplex Φ φ).obj A).X p).val.obj (op Z))) :
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
        ((postSlicePushComplex Φ φ).obj B)).sectionsIso W).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((postSliceSectionIso Φ φ hff A B W).hom.f n) s)).v p q hpq).val.app
          (op (Over.mk g)) x =
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X A B).sectionsIso (Φ.obj W)).hom.f n) s).v
        p q hpq).val.app (op (Over.mk m)) x := by
  subst hm
  exact postSliceSectionIso_apply_section Φ φ hff A B W n p q hpq s g x

/-- The structure map `φ` is natural: restricting a section of `O_C` along `g` and pushing it
forward is pushing it forward and restricting along the image of `g`. -/
theorem postSlice_phi_naturality_apply {Z W : Y.C} (g : Z ⟶ W)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op W)) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (Φ.map g).op (φ.hom.app (op W) r) =
      φ.hom.app (op Z) ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g.op r) :=
  (congrArg (fun m => (RingCat.Hom.hom m) r) (φ.hom.naturality g.op)).symm

/-- `postSliceSectionIso` is linear for the action of the structure sheaf of `C`, the source
being a module over it through the structure map `φ`. -/
def postSliceSectionLinearEquiv (W : Y.C) (n : ℤ) :
    ((((postSlicePushComplex Φ φ).obj (sheafHomComplex X A B).obj).X n).val.obj (op W))
        ≃ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op W)]
      (((sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
        ((postSlicePushComplex Φ φ).obj B)).obj.X n).val.obj (op W)) where
  toFun := AddCommGrpCat.Hom.hom ((postSliceSectionIso Φ φ hff A B W).hom.f n)
  invFun := AddCommGrpCat.Hom.hom ((postSliceSectionIso Φ φ hff A B W).inv.f n)
  left_inv := Iso.hom_inv_id_apply ((HomologicalComplex.eval _ _ n).mapIso
    (postSliceSectionIso Φ φ hff A B W))
  right_inv := Iso.inv_hom_id_apply ((HomologicalComplex.eval _ _ n).mapIso
    (postSliceSectionIso Φ φ hff A B W))
  map_add' := map_add _
  map_smul' r s := by
    apply sheafHomSection_ext (sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
      ((postSlicePushComplex Φ φ).obj B)) W n
    intro p q hpq T x
    obtain ⟨T⟩ := T
    obtain ⟨Z, g, rfl⟩ := Over.mk_surjective T
    simp only [RingHom.id_apply]
    rw [postSliceSectionIso_apply_section Φ φ hff A B W n p q hpq (r • s) g x]
    rw [(sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
      ((postSlicePushComplex Φ φ).obj B)).smul_natural W r n p q hpq _ g x]
    rw [postSliceSectionIso_apply_section Φ φ hff A B W n p q hpq s g x]
    refine Eq.trans ((sheafHomComplex X A B).smul_natural (Φ.obj W)
      (φ.hom.app (op W) r) n p q hpq s (Φ.map g) x) ?_
    rw [postSlice_phi_naturality_apply Φ φ g r]
    rfl

/-- `postSliceSectionLinearEquiv` is compatible with restriction along an arrow of `C`. -/
theorem postSliceSectionLinearEquiv_natural (n : ℤ) {Z W : Y.C} (g : Z ⟶ W)
    (s : ((((postSlicePushComplex Φ φ).obj (sheafHomComplex X A B).obj).X n).val.obj (op W))) :
    postSliceSectionLinearEquiv Φ φ hff A B Z n
        ((((postSlicePushComplex Φ φ).obj (sheafHomComplex X A B).obj).X n).val.map g.op s) =
      (((sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
        ((postSlicePushComplex Φ φ).obj B)).obj.X n).val.map g.op)
        (postSliceSectionLinearEquiv Φ φ hff A B W n s) := by
  apply sheafHomSection_ext (sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
    ((postSlicePushComplex Φ φ).obj B)) Z n
  intro p q hpq T x
  obtain ⟨T⟩ := T
  obtain ⟨Z', h, rfl⟩ := Over.mk_surjective T
  have hLHS := postSliceSectionIso_apply_section Φ φ hff A B Z n p q hpq
    ((((postSlicePushComplex Φ φ).obj (sheafHomComplex X A B).obj).X n).val.map g.op s) h x
  have hX := (sheafHomComplex X A B).restrict_natural (Φ.map g) n p q hpq s (Φ.map h) x
  have hW := postSliceSectionIso_apply_section_of_eq Φ φ hff A B W n p q hpq s (h ≫ g)
    (Φ.map h ≫ Φ.map g) (Φ.map_comp h g).symm x
  have hY := (sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
    ((postSlicePushComplex Φ φ).obj B)).restrict_natural g n p q hpq
      (AddCommGrpCat.Hom.hom
        ((postSliceSectionIso Φ φ hff A B W).hom.f n) s) h x
  exact hLHS.trans (hX.symm.trans (hW.symm.trans hY))

/-- **The internal Hom complex is carried along a functor which is an equivalence on slices.**
The transport along `φ` of the internal Hom complex `SheafHom(A, B)` is the internal Hom complex
of the transports; degreewise on sections it is `postSliceSectionIso`, which on each local
homogeneous component is the transport along the slice functor. -/
def postSliceSheafHomComplexIso :
    (postSlicePushComplex Φ φ).obj (sheafHomComplex X A B).obj ≅
      (sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
        ((postSlicePushComplex Φ φ).obj B)).obj := by
  let e (n : ℤ) :
      (((postSlicePushComplex Φ φ).obj (sheafHomComplex X A B).obj).X n).val ≅
        ((sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
          ((postSlicePushComplex Φ φ).obj B)).obj.X n).val :=
    PresheafOfModules.isoMk
      (fun W => (postSliceSectionLinearEquiv Φ φ hff A B W.unop n).toModuleIso)
      (by
        intro W Z f
        ext s
        exact postSliceSectionLinearEquiv_natural Φ φ hff A B n f.unop s)
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (SheafOfModules.fullyFaithfulForget _).preimageIso (e n)) ?_
  intro i j hij
  ext W s
  exact ConcreteCategory.congr_hom
    ((postSliceSectionIso Φ φ hff A B W.unop).hom.comm i j) s

end

/-- **The chain-level transport is natural in both variables.** -/
theorem postSliceSheafHomComplexIso_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (f : A' ⟶ A) (g : B ⟶ B') :
    (postSlicePushComplex Φ φ).map (homMap X f g) ≫
        (postSliceSheafHomComplexIso Φ φ hff A' B').hom =
      (postSliceSheafHomComplexIso Φ φ hff A B).hom ≫
        homMap Y ((postSlicePushComplex Φ φ).map f) ((postSlicePushComplex Φ φ).map g) := by
  ext n V s
  apply sheafHomSection_ext_v (sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A')
    ((postSlicePushComplex Φ φ).obj B')) V.unop n
  intro p q hpq
  show (AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A')
        ((postSlicePushComplex Φ φ).obj B')).sectionsIso V.unop).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((postSliceSectionIso Φ φ hff A' B' V.unop).hom.f n)
        (((homMap X f g).f n).val.app (op (Φ.obj V.unop)) s))).v p q hpq =
    (AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A')
        ((postSlicePushComplex Φ φ).obj B')).sectionsIso V.unop).hom.f n)
      (((homMap Y ((postSlicePushComplex Φ φ).map f)
        ((postSlicePushComplex Φ φ).map g)).f n).val.app
        (op V.unop)
        (AddCommGrpCat.Hom.hom
          ((postSliceSectionIso Φ φ hff A B V.unop).hom.f n) s))).v p q hpq
  rw [postSliceSectionIso_apply Φ φ hff A' B' V.unop n p q hpq
    (((homMap X f g).f n).val.app (op (Φ.obj V.unop)) s)]
  rw [sectionsIso_homMap_v X f g (Φ.obj V.unop) n p q hpq s]
  rw [sectionsIso_homMap_v Y ((postSlicePushComplex Φ φ).map f) ((postSlicePushComplex Φ φ).map g)
    V.unop n p q hpq (AddCommGrpCat.Hom.hom
      ((postSliceSectionIso Φ φ hff A B V.unop).hom.f n) s)]
  rw [postSliceSectionIso_apply Φ φ hff A B V.unop n p q hpq s]
  simp only [Functor.map_comp]
  rfl

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]
  (hK : ∀ I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
    I.IsKInjective → ((postSlicePushComplex Φ φ).obj I).IsKInjective)

/-- The source of the transport of the derived internal Hom along an exact functor `P` of
modules, as a functor of both arguments: `(K, L) ↦ P RSheafHom(K, L)`. -/
abbrev postSliceSourceFunctor
    (P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P] :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  Functor.uncurry.obj (derivedSheafHomBifunctor X) ⋙ P.mapDerivedCategory

/-- The target of the transport of the derived internal Hom along an exact functor `P` of
modules, as a functor of both arguments: `(K, L) ↦ RSheafHom(P K, P L)`. -/
abbrev postSliceTargetFunctor
    (P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P] :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (P.mapDerivedCategory.op.prod P.mapDerivedCategory) ⋙
    Functor.uncurry.obj (derivedSheafHomBifunctor Y)

/-- The transport of the class of a complex is the class of its transport. -/
abbrev postSliceComparison
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj (DerivedCategory.Q.obj A) ≅
      DerivedCategory.Q.obj ((postSlicePushComplex Φ φ).obj A) :=
  (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app A

/-- The comparison of `postSliceComparison` is natural in the complex. -/
theorem postSliceComparison_natural
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ B) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
        (postSliceComparison Φ φ B).hom =
      (postSliceComparison Φ φ A).hom ≫
        DerivedCategory.Q.map ((postSlicePushComplex Φ φ).map f) :=
  (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.hom.naturality f

/-- The source of the transport on a K-injective model: the transport of the class of the
internal Hom complex. -/
def postSliceSourceComparison
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    (postSliceSourceFunctor (SheafOfModules.pushforward.{u} φ)).obj
        (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≅
      DerivedCategory.Q.obj ((postSlicePushComplex Φ φ).obj (sheafHomComplex X A B).obj) :=
  (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso
      (derivedSheafHomComparison X A B) ≪≫
    postSliceComparison Φ φ (sheafHomComplex X A B).obj

/-- The transport of classes of complexes in both arguments of the derived internal Hom of the
source site, as an isomorphism of functors on pairs of complexes. -/
def postSliceArgumentsComparison :
    ((DerivedCategory.Q ⋙ (SheafOfModules.pushforward.{u} φ).mapDerivedCategory).op.prod
      (DerivedCategory.Q ⋙ (SheafOfModules.pushforward.{u} φ).mapDerivedCategory)) ⋙
        Functor.uncurry.obj (derivedSheafHomBifunctor Y) ≅
    ((postSlicePushComplex Φ φ ⋙ DerivedCategory.Q).op.prod
        (postSlicePushComplex Φ φ ⋙ DerivedCategory.Q)) ⋙
      Functor.uncurry.obj (derivedSheafHomBifunctor Y) :=
  Functor.isoWhiskerRight (NatIso.prod
    (NatIso.op (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.symm)
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors) _

include hK in
/-- The target of the transport on a K-injective model: the class of the internal Hom complex
of the transports. -/
def postSliceTargetComparison
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [hB : B.IsKInjective] :
    (postSliceTargetFunctor (SheafOfModules.pushforward.{u} φ)).obj
        (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≅
      DerivedCategory.Q.obj
        (sheafHomComplex Y ((postSlicePushComplex Φ φ).obj A)
          ((postSlicePushComplex Φ φ).obj B)).obj :=
  haveI := hK B hB
  (postSliceArgumentsComparison Φ φ).app (op A, B) ≪≫
    derivedSheafHomComparison Y ((postSlicePushComplex Φ φ).obj A)
      ((postSlicePushComplex Φ φ).obj B)

/-- The source model comparison is natural in both complexes. -/
theorem postSliceSourceComparison_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} [B.IsKInjective]
    [B'.IsKInjective] (f : A' ⟶ A) (g : B ⟶ B') :
    (postSliceSourceFunctor (SheafOfModules.pushforward.{u} φ)).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (postSliceSourceComparison Φ φ A' B').hom =
    (postSliceSourceComparison Φ φ A B).hom ≫
      DerivedCategory.Q.map ((postSlicePushComplex Φ φ).map (homMap X f g)) := by
  show (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
      (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map f).op).app
          (DerivedCategory.Q.obj B) ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
          (DerivedCategory.Q.map g)) ≫
      ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
          (derivedSheafHomComparison X A' B').hom ≫ _) =
    ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (derivedSheafHomComparison X A B).hom ≫ _) ≫ _
  rw [← Functor.map_comp_assoc, Category.assoc, derivedSheafHomComparison_naturality X f g,
    Functor.map_comp, Category.assoc, postSliceComparison_natural, Category.assoc]

/-- The target model comparison is natural in both complexes. -/
theorem postSliceTargetComparison_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} [hB : B.IsKInjective]
    [hB' : B'.IsKInjective] (f : A' ⟶ A) (g : B ⟶ B') :
    (postSliceTargetFunctor (SheafOfModules.pushforward.{u} φ)).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (postSliceTargetComparison Φ φ hK A' B').hom =
    (postSliceTargetComparison Φ φ hK A B).hom ≫
      DerivedCategory.Q.map (homMap Y ((postSlicePushComplex Φ φ).map f)
        ((postSlicePushComplex Φ φ).map g)) := by
  have := hK B hB
  have := hK B' hB'
  simp only [postSliceTargetComparison, Iso.trans_hom, Iso.app_hom]
  have h : (postSliceTargetFunctor (SheafOfModules.pushforward.{u} φ)).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (postSliceArgumentsComparison Φ φ).hom.app (op A', B') = _ :=
    (postSliceArgumentsComparison Φ φ).hom.naturality (Prod.mkHom f.op g)
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  congr 1
  simp only [Functor.comp_obj, Functor.prod_obj, Functor.op_obj, Functor.uncurry_obj_obj,
    Functor.comp_map, Functor.prod_map, Functor.op_map,
    Quiver.Hom.unop_op, Functor.uncurry_obj_map]
  simpa only [Category.assoc] using
    derivedSheafHomComparison_naturality Y ((postSlicePushComplex Φ φ).map f)
      ((postSlicePushComplex Φ φ).map g)

/-- The transport of the derived internal Hom on a pair of complexes with K-injective target. -/
def postSliceModelIso
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    (postSliceSourceFunctor (SheafOfModules.pushforward.{u} φ)).obj
        (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≅
      (postSliceTargetFunctor (SheafOfModules.pushforward.{u} φ)).obj
          (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) :=
  postSliceSourceComparison Φ φ A B ≪≫
    DerivedCategory.Q.mapIso (postSliceSheafHomComplexIso Φ φ hff A B) ≪≫
    (postSliceTargetComparison Φ φ hK A B).symm

/-- The model transport is natural in both complexes. -/
theorem postSliceModelIso_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} [B.IsKInjective]
    [B'.IsKInjective] (f : A' ⟶ A) (g : B ⟶ B') :
    (postSliceSourceFunctor (SheafOfModules.pushforward.{u} φ)).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (postSliceModelIso Φ φ hff hK A' B').hom =
    (postSliceModelIso Φ φ hff hK A B).hom ≫
      (postSliceTargetFunctor (SheafOfModules.pushforward.{u} φ)).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) := by
  apply (cancel_mono (postSliceTargetComparison Φ φ hK A' B').hom).mp
  simp only [postSliceModelIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, postSliceSourceComparison_natural Φ φ f g, Category.assoc,
    postSliceTargetComparison_natural Φ φ hK f g]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, postSliceSheafHomComplexIso_natural]

include hff hK in
/-- **The derived internal Hom is carried along a functor which is an equivalence on slices,
naturally in both arguments**, by an isomorphism of functors of two variables which on a pair
of complexes with K-injective target is the class of the chain-level transport
`postSliceSheafHomComplexIso`. It is obtained, as in
`AlgebraicGeometry.RingedSite.derivedHom_restriction_exists`, by extending the model transport
`postSliceModelIso` along the functorial K-injective resolution. -/
theorem postSliceDerivedSheafHom_exists :
    ∃ e : postSliceSourceFunctor (SheafOfModules.pushforward.{u} φ) ≅
        postSliceTargetFunctor (SheafOfModules.pushforward.{u} φ),
      ∀ (A B : CochainComplex (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) [B.IsKInjective],
        e.hom.app (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) =
          (postSliceModelIso Φ φ hff hK A B).hom := by
  let C := CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ
  let Q : C ⥤ DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := DerivedCategory.Q
  let W := HomologicalComplex.quasiIso (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
  let R := (𝟭 Cᵒᵖ).prod (Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  let η : 𝟭 (Cᵒᵖ × C) ⟶ R :=
    { app := fun c => Prod.mkHom (𝟙 c.1)
        ((Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app c.2)
      naturality := by
        intro c c' f
        apply Prod.ext
        · simp [R]
        · exact (Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).naturality f.2 }
  have (c : Cᵒᵖ × C) : IsIso ((Q.op.prod Q).map (η.app c)) := by
    dsimp [Q, η]
    exact (isIso_prod_iff _ _).2 ⟨(Q.mapIso (Iso.refl c.1.unop)).op.isIso_hom, inferInstance⟩
  obtain ⟨e, he⟩ := extendIsoFromResolution (Q.op.prod Q) (W.op.prod W) R η
    (fun c : Cᵒᵖ × C => c.2.IsKInjective)
    (fun c => Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) c.2)
    (postSliceSourceFunctor (SheafOfModules.pushforward.{u} φ))
    (postSliceTargetFunctor (SheafOfModules.pushforward.{u} φ))
    (fun c hc => by
      have := hc
      exact postSliceModelIso Φ φ hff hK c.1.unop c.2)
    (by
      intro c c' hc hc' f
      have := hc
      have := hc'
      exact postSliceModelIso_natural Φ φ hff hK f.1.unop f.2)
  exact ⟨e, fun A B hB => he (op A, B) hB⟩

/-- **The derived internal Hom is carried along a functor which is an equivalence on slices.**
The transport along `φ` of `RSheafHom_{O_D}(K, L)` is the derived internal Hom of the
transports of `K` and `L`, naturally in both (`postSliceDerivedSheafHomNatIso_natural_left`,
`postSliceDerivedSheafHomNatIso_natural_right`); on a pair of complexes with K-injective target
it is the class of the chain-level transport `postSliceSheafHomComplexIso`
(`postSliceDerivedSheafHomNatIso_model`). -/
def postSliceDerivedSheafHomNatIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj
        (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).obj
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) :=
  (Classical.choose (postSliceDerivedSheafHom_exists Φ φ hff hK)).app (op K, L)

/-- On a pair of complexes with K-injective target the transport is the model transport. -/
theorem postSliceDerivedSheafHomNatIso_model
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    (postSliceDerivedSheafHomNatIso Φ φ hff hK (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj B)).hom = (postSliceModelIso Φ φ hff hK A B).hom :=
  Classical.choose_spec (postSliceDerivedSheafHom_exists Φ φ hff hK) A B

/-- The transport of the derived internal Hom is natural in the first, contravariant argument. -/
theorem postSliceDerivedSheafHomNatIso_natural_left
    {K K' L : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (f : K' ⟶ K) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).map f.op).app L) ≫
        (postSliceDerivedSheafHomNatIso Φ φ hff hK K' L).hom =
      (postSliceDerivedSheafHomNatIso Φ φ hff hK K L).hom ≫
        ((derivedSheafHomBifunctor Y).map
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map f).op).app
            ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) := by
  have h := (Classical.choose (postSliceDerivedSheafHom_exists Φ φ hff hK)).hom.naturality
    (Prod.mkHom f.op (𝟙 L))
  simpa [postSliceDerivedSheafHomNatIso] using h

/-- The transport of the derived internal Hom is natural in the second, covariant argument. -/
theorem postSliceDerivedSheafHomNatIso_natural_right
    {K L L' : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (g : L ⟶ L') :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).obj (op K)).map g) ≫
        (postSliceDerivedSheafHomNatIso Φ φ hff hK K L').hom =
      (postSliceDerivedSheafHomNatIso Φ φ hff hK K L).hom ≫
        ((derivedSheafHomBifunctor Y).obj
          (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).map
            ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map g) := by
  have h := (Classical.choose (postSliceDerivedSheafHom_exists Φ φ hff hK)).hom.naturality
    (Prod.mkHom (𝟙 (op K)) g)
  simpa [postSliceDerivedSheafHomNatIso] using h

end Derived

end AlgebraicGeometry.RingedSite

end
