module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasis
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.ModuleValuedComplex
-- The Čech reindexing isomorphism below compares two spellings of a product; the defeq
-- fails with `getLimitCone` reported as not exposed, which is the module system rather than
-- transparency, so the bodies are imported.
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Vanishing of sheaf cohomology from vanishing of Čech cohomology

If the positive-degree Čech cohomology of a sheaf of modules vanishes for every open
covering, then its positive-degree cohomology over every open also vanishes.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Cohomology.CechVanishing.isZero_rightDerived_sections_of_isZero_cechHomology` is the
  Čech-vanishing criterion for higher cohomology.
* `Stacks.Cohomology.CechVanishing.hasSheafifyOpensUnivLE`,
  `Stacks.Cohomology.CechVanishing.wEqualsLocallyBijectiveOpensUnivLE` and
  `Stacks.Cohomology.CechVanishing.enoughInjectivesSheafOfModulesUnivLE` are the three
  conditions that make that right derived functor expressible, for the site of opens of a space
  in `Type u` and a coefficient universe `v` with `UnivLE.{u, v}`. They are instances, so the
  criterion assumes none of them.

## Implementation notes

The structure sheaf is allowed to be any sheaf of rings. Cohomology over an open is expressed
as the right derived functor of the additive functor of sections of the underlying sheaf of
abelian groups. The coefficient universe `v` is a parameter of its own, tied to the space
universe `u` only by `UnivLE.{u, v}`: that is what makes `SheafOfModules.{v} R` locally
`v`-small, hence Grothendieck abelian with enough injectives, so no abelianness or
injective-resolution hypothesis is assumed. At `v = u`, the single universe of the Stacks
Project, `UnivLE.{u, u}` is itself an instance and the criterion has no instance argument at
all. Covering families are
indexed in `Type (max u v)`, which includes indices from the space universe. For Čech cohomology,
the underlying abelian-group presheaf is lifted to this universe so that the required products
exist. Since every family of opens covers its supremum, quantifying over all covers is
equivalently expressed by quantifying over all families of opens.

The universe relation is carried as `UnivLE.{u, v}` and not by writing the coefficient universe
as `max u v`: `max u v' =?= v` is a universe *equation*, which Lean does not solve, so a
conclusion of that shape cannot be instantiated at a prescribed coefficient universe, whereas a
`UnivLE` hypothesis specializes to `v = u` and to every `v` above `u` alike. The separator that
the enough-injectives instance rests on is stated at a prescribed universe for the same reason;
see `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SeparatorUnivLE.lean`.

Because the indexing type of a cover of a space in `Type u` lies in `Type u`, the Čech products
needed to run Tag 01EW live in `AddCommGrpCat.{max u v}` and not in `AddCommGrpCat.{v}`. The
argument therefore lifts the sheaf of modules along `ULift` to `SheafOfModules.{max u v} R`,
applies Tag 01EW there, and transports the conclusion back down. The descent is *not* made
through the derived category: a flasque resolution is used instead, so that
`CategoryTheory.InjectiveResolution.isoRightDerivedObjOfQuasiIso` computes both right derived
functors from one and the same complex. The class of sheaves of modules with flasque underlying
abelian sheaf is adapted to the sections functor by Mathlib's
`TopCat.Sheaf.IsFlasque.epi_of_shortExact` and `of_shortExact_of_isFlasque₁₂` together with
Tag 01EP's `underlying_isFlasque`.

## References

* [Stacks Project, Tag 01EV](https://stacks.math.columbia.edu/tag/01EV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TopCat TopCat.Presheaf TopCat.Sheaf
open scoped AlgebraicGeometry

universe v u r

namespace Stacks.Cohomology.CechVanishing

/-! ### The universe lift on presheaves and sheaves of modules -/

/-- Sections of an abelian sheaf over an open are additive in the sheaf. -/
instance sheafSections_additive
    {X : Type u} [TopologicalSpace X] (U : Opens X) :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
      (op U)).Additive := by
  rw [show (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj (op U) =
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{v}).obj (op U) from rfl]
  infer_instance

/-- A presheaf of modules with carriers in `Type v`, lifted termwise to `Type (max u v)`. -/
private noncomputable def liftPresheafOfModules {X : Type u} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (F : PresheafOfModules.{v} R.obj) : PresheafOfModules.{max u v} R.obj where
  obj U := ModuleCat.of _ (ULift.{u} (F.obj U))
  map {U V} f := ModuleCat.ofHom
    (R := R.obj.obj U)
    (X := ModuleCat.of (R.obj.obj U) (ULift.{u} (F.obj U)))
    (Y := (ModuleCat.restrictScalars ((R.obj.map f).hom)).obj
      (ModuleCat.of (R.obj.obj V) (ULift.{u} (F.obj V))))
    { toFun := fun m ↦ ULift.up (F.map f m.down)
      map_add' := by intros; exact congrArg ULift.up ((F.map f).hom.map_add _ _)
      map_smul' := by intros; exact congrArg ULift.up (F.map_smul f _ _) }
  map_id U := by
    ext m
    change ULift.up (F.map (𝟙 U) m.down) = m
    rw [F.map_id]
    rfl
  map_comp f g := by ext m; exact congrArg ULift.up (F.map_comp_apply f g m.down)

/-- The lift of a morphism of presheaves of modules. -/
private noncomputable def liftPresheafOfModulesMap {X : Type u} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    {F G : PresheafOfModules.{v} R.obj} (f : F ⟶ G) :
    liftPresheafOfModules F ⟶ liftPresheafOfModules G where
  app U := ModuleCat.ofHom {
    toFun := fun x => ULift.up (f.app U x.down)
    map_add' := by intros; exact congrArg ULift.up ((f.app U).hom.map_add _ _)
    map_smul' := by intros; exact congrArg ULift.up ((f.app U).hom.map_smul _ _)
  }
  naturality := by
    intro U V f'
    apply ModuleCat.hom_ext
    ext x
    exact congrArg ULift.up <| congrArg (fun h => h x.down) (f.naturality f')

/-- The universe lift as a functor on presheaves of modules. -/
private noncomputable def liftPresheafOfModulesFunctor {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}) :
    PresheafOfModules.{v} R.obj ⥤ PresheafOfModules.{max u v} R.obj where
  obj := liftPresheafOfModules
  map := liftPresheafOfModulesMap
  map_id := by intros; ext U x; rfl
  map_comp := by intros; ext U x; rfl

private noncomputable instance liftPresheafOfModulesFunctor_preservesFiniteLimits
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}) :
    Limits.PreservesFiniteLimits (liftPresheafOfModulesFunctor R) where
  preservesFiniteLimits J _ _ := {
    preservesLimit := fun {F} => {
      preserves := fun {c} hc => by
        apply Nonempty.intro
        apply PresheafOfModules.evaluationJointlyReflectsLimits
        intro U
        change IsLimit (((PresheafOfModules.evaluation R.obj U ⋙
          ModuleCat.uliftFunctor.{u, v} (R.obj.obj U)).mapCone c))
        exact isLimitOfPreserves (ModuleCat.uliftFunctor.{u, v} (R.obj.obj U))
          (isLimitOfPreserves (PresheafOfModules.evaluation R.obj U) hc)
    }
  }

/-- A sheaf of modules with carriers in `Type v`, lifted termwise to `Type (max u v)`. -/
private noncomputable def liftSheafOfModules {X : Type u} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (F : SheafOfModules.{v} R) : SheafOfModules.{max u v} R where
  val := liftPresheafOfModules F.val
  isSheaf := Presheaf.isSheaf_comp_of_isSheaf _ F.val.presheaf
    AddCommGrpCat.uliftFunctor.{u, v} F.isSheaf

/-- The universe lift as a functor on sheaves of modules. -/
private noncomputable def liftSheafOfModulesFunctor {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}) :
    SheafOfModules.{v} R ⥤ SheafOfModules.{max u v} R where
  obj := liftSheafOfModules
  map f := ⟨liftPresheafOfModulesMap f.val⟩
  map_id := by intros; ext U x; rfl
  map_comp := by intros; ext U x; rfl

private noncomputable instance liftSheafOfModulesFunctor_preservesFiniteLimits
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}) :
    Limits.PreservesFiniteLimits (liftSheafOfModulesFunctor R) := by
  let e : liftSheafOfModulesFunctor R ⋙ SheafOfModules.forget R ≅
      SheafOfModules.forget R ⋙ liftPresheafOfModulesFunctor R :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  let _ : Limits.PreservesFiniteLimits
      (liftSheafOfModulesFunctor R ⋙ SheafOfModules.forget R) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (liftSheafOfModulesFunctor R) (SheafOfModules.forget R)

/-- The abelian presheaf underlying the lift of `F` is the termwise `ULift` of the abelian
presheaf underlying `F`. -/
private noncomputable def liftUnderlyingPresheafIso {X : Type u} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (F : SheafOfModules.{v} R) :
    ((SheafOfModules.toSheaf R ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
      (liftSheafOfModules F)) ≅
      (F.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u, v}) := by
  refine NatIso.ofComponents (fun U => Iso.refl _) ?_
  intro U V f
  ext x
  rfl

private lemma locallySurjective_ulift_iff {C : Type u} [Category.{r} C]
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (η : P ⟶ Q) :
    Presheaf.IsLocallySurjective J
        (Functor.whiskerRight η AddCommGrpCat.uliftFunctor.{u, v}) ↔
      Presheaf.IsLocallySurjective J η := by
  have heq (U : C) (x : Q.obj (op U)) :
      Presheaf.imageSieve
          (Functor.whiskerRight η AddCommGrpCat.uliftFunctor.{u, v}) (ULift.up x) =
        Presheaf.imageSieve η x := by
    ext V f
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y.down, congrArg ULift.down hy⟩,
      fun ⟨y, hy⟩ ↦ ⟨ULift.up y, congrArg ULift.up hy⟩⟩
  constructor
  · intro h
    constructor
    intro U x
    rw [← heq U x]
    exact Presheaf.imageSieve_mem J _ _
  · intro h
    constructor
    intro U x
    rw [show x = ULift.up x.down from rfl, heq]
    exact Presheaf.imageSieve_mem J η _

private lemma sheafCompose_ulift_preservesEpimorphisms
    {X : Type u} [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    Functor.PreservesEpimorphisms
      (sheafCompose (Opens.grothendieckTopology X)
        AddCommGrpCat.uliftFunctor.{u, v}) := by
  let J := Opens.grothendieckTopology X
  let E := sheafCompose J AddCommGrpCat.uliftFunctor.{u, v}
  constructor
  intro F G f hf
  have hlow : Presheaf.IsLocallySurjective J f.hom :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
      (J := J) (A := AddCommGrpCat.{v}) (φ := f)).mpr hf
  have hlocal : CategoryTheory.Sheaf.IsLocallySurjective (E.map f) := by
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight f.hom AddCommGrpCat.uliftFunctor.{u, v})
    exact (locallySurjective_ulift_iff J f.hom).2 hlow
  exact (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
    (J := J) (A := AddCommGrpCat.{max u v}) (φ := E.map f)).mp hlocal

private noncomputable instance liftSheafOfModulesFunctor_preservesEpimorphisms
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    Functor.PreservesEpimorphisms (liftSheafOfModulesFunctor R) := by
  constructor
  intro F G f hf
  let J := Opens.grothendieckTopology X
  let Tlo := SheafOfModules.toSheaf R
  let Thi := SheafOfModules.toSheaf.{max u v} R
  let E := sheafCompose J AddCommGrpCat.uliftFunctor.{u, v}
  let e : liftSheafOfModulesFunctor R ⋙ Thi ≅ Tlo ⋙ E :=
    NatIso.ofComponents (fun M =>
      (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{max u v}).preimageIso
        (liftUnderlyingPresheafIso M)) (by
          intro M N g
          apply (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{max u v}).map_injective
          ext U x
          rfl)
  have hE : Epi (E.map (Tlo.map f)) := by
    let _ : E.PreservesEpimorphisms := sheafCompose_ulift_preservesEpimorphisms
    infer_instance
  have hThi : Epi (Thi.map ((liftSheafOfModulesFunctor R).map f)) := by
    rw [show Thi.map ((liftSheafOfModulesFunctor R).map f) =
        (e.app F).hom ≫ E.map (Tlo.map f) ≫ (e.app G).inv by ext U x; rfl]
    infer_instance
  refine ⟨fun {Z} g h hgh => ?_⟩
  apply Thi.map_injective
  apply (cancel_epi (Thi.map ((liftSheafOfModulesFunctor R).map f))).mp
  simpa only [Functor.map_comp] using congrArg Thi.map hgh

private noncomputable instance liftSheafOfModulesFunctor_additive
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}) :
    (liftSheafOfModulesFunctor R).Additive where
  map_add := by
    intro F G f g
    ext U x
    rfl

private noncomputable instance liftSheafOfModulesFunctor_preservesHomology
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    Functor.PreservesHomology (liftSheafOfModulesFunctor R) := by
  let L := liftSheafOfModulesFunctor R
  let _ : L.PreservesZeroMorphisms := ⟨by intros; ext U x; rfl⟩
  exact Functor.preservesHomology_of_preservesEpis_and_kernels L

/-! ### Sheaves of modules with flasque underlying abelian sheaf

This class of objects is adapted, in the sense of [Stacks 05T8], to the functor of sections over
any open. It is used to compute the right derived functors of sections on both sides of the
universe lift from one and the same complex. -/

/-- The abelian sheaf underlying a sheaf of modules whose carriers are in `Type (max u v)`. -/
private noncomputable abbrev highUnderlyingSheaf {X : Type u} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (F : SheafOfModules.{max u v} R) :
    TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X) :=
  (SheafOfModules.toSheaf R).obj F

/-- The abelian sheaf underlying the universe lift of a sheaf of modules. -/
private noncomputable abbrev liftUnderlyingSheaf {X : Type u} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (F : SheafOfModules.{v} R) :
    TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X) :=
  (SheafOfModules.toSheaf R).obj (liftSheafOfModules F)

/-- The abelian sheaf underlying an injective sheaf of modules is flasque. This is Tag 01EP's
`underlying_isFlasque`, restated for the repackaging of a sheaf on a site as a sheaf on a
space. -/
@[ega "0 12.2.1" "partial", sga "4 V 4.6" "special case"]
private theorem highInjective_underlying_isFlasque {X : Type u} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (I : SheafOfModules.{max u v} R) [Injective I] :
    (highUnderlyingSheaf I).IsFlasque :=
  Stacks.Cohomology.CechSheaf.underlying_isFlasque I

/-- The abelian sheaf underlying the universe lift of an injective sheaf of modules is flasque:
restriction is surjective by Tag 01EA, and `ULift` preserves surjectivity. -/
@[ega "0 12.2.1" "partial", sga "4 V 4.6" "special case"]
private theorem liftInjective_underlying_isFlasque {X : Type u} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (I : SheafOfModules.{v} R) [Injective I] :
    (liftUnderlyingSheaf I).IsFlasque := by
  constructor
  intro U V f
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  obtain ⟨x, hx⟩ :=
    Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective R I
      (leOfHom f.unop) y.down
  exact ⟨ULift.up x, congrArg ULift.up hx⟩

/-! ### Flasqueness for coefficients above the space universe

Mathlib's `TopCat.Sheaf.IsFlasque.epi_of_shortExact` and `of_shortExact_of_isFlasque₁₂` are stated
with the coefficient category pinned to `AddCommGrpCat.{u}` for `X : TopCat.{u}`, so they do not
apply to the sheaves in `AddCommGrpCat.{max u r}` that the universe lift produces. The two
statements are reproved here with the coefficient universe free. The arguments are Mathlib's. -/

/-- Pairs of an open subset of `U` and a section over it mapping to the restriction of `s`. -/
private abbrev FlasqueUnder {X : TopCat.{u}} {U : Opens X}
    {F G : TopCat.Sheaf AddCommGrpCat.{max u r} X} (g : F ⟶ G)
    (s : G.obj.obj (op U)) :=
  StructuredArrow (Functor.elementsMk _ _ s) (Functor.whiskerRight g.hom
    (CategoryTheory.forget AddCommGrpCat.{max u r})).mapElements

/-- The category structure on `FlasqueUnder`, supplied explicitly. Instance search does not find
it: `Functor.Elements` is a semireducible `def`, so with the base point written as an anonymous
constructor `⟨op U, s⟩` the elaborator cannot see that it is a point of the category the
`StructuredArrow` is taken over, and the search for `Quiver (FlasqueUnder g s)` fails. Supplying
the instance makes the elaborator check the definitional equality instead of searching for it;
the same statement with a named base point needs nothing. -/
private instance flasqueUnderCategory {X : TopCat.{u}} {U : Opens X}
    {F G : TopCat.Sheaf AddCommGrpCat.{max u r} X} (g : F ⟶ G)
    (s : G.obj.obj (op U)) : Category.{u} (FlasqueUnder g s) :=
  CategoryTheory.instCategoryStructuredArrow

/-- Chains in `FlasqueUnder g s` are bounded above, by gluing the sections of the chain. -/
private lemma flasque_under_chains_bounded {X : TopCat.{u}}
    {U : Opens X} {F G : TopCat.Sheaf AddCommGrpCat.{max u r} X} (g : F ⟶ G)
    [HasLimitsOfSize.{u, u} AddCommGrpCat.{max u r}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u r}]
    (s : G.obj.obj (op U)) (c : Set (FlasqueUnder g s))
    (hc : IsChain (fun x y ↦ Nonempty (y ⟶ x)) c) :
    ∃ ub, ∀ a ∈ c, Nonempty (ub ⟶ a) := by
  let f : c → Opens X := fun x ↦ x.1.right.1.unop
  obtain ⟨t, ht, _⟩ : ∃! s₁, IsGluing F.obj f (fun x ↦ x.val.right.2) s₁ := by
    refine Sheaf.existsUnique_gluing F _ _ (fun i j ↦ ?_)
    obtain (rfl | h₁ | h₁) : i = j ∨ Nonempty (i.val ⟶ j.val) ∨ Nonempty (j.val ⟶ i.val) :=
      (em (i = j)).imp_right fun hij ↦ (hc i.property j.property fun he ↦ hij (Subtype.ext he)).symm
    · rfl
    all_goals
      rw [← h₁.some.2.map_val]
      dsimp
      rw [← Functor.map_comp_apply]
      rfl
  have le₁ : iSup f ≤ U := iSup_le fun j ↦ leOfHom j.1.hom.1.unop
  have le₂ : ∀ i, i ∈ c → unop i.right.1 ≤ iSup f := fun i hi ↦ le_iSup f ⟨i, hi⟩
  use StructuredArrow.mk (Functor.Elements.homMk (homOfLE le₁).op
    (eq_app_of_locally_eq ht (fun i ↦ leOfHom i.1.hom.1.unop)
      (fun i ↦ (i.1.hom.map_val).symm)).symm :
      Functor.elementsMk _ _ s ⟶ (Functor.whiskerRight g.hom
        (CategoryTheory.forget AddCommGrpCat.{max u r})).mapElements.obj (Functor.elementsMk _ _ t))
  exact fun i hi ↦ ⟨StructuredArrow.homMk (Functor.Elements.homMk
    (homOfLE (le₂ i hi)).op (ht ⟨i, hi⟩)) (by cat_disch)⟩

/-- Given a short exact sequence of abelian sheaves with flasque first term, sections over any
open of the third term are hit by sections of the second. -/
private theorem epi_of_shortExact_generic {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{max u r} X)}
    [HasLimitsOfSize.{u, u} AddCommGrpCat.{max u r}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u r}]
    (hS : S.ShortExact) [S.X₁.IsFlasque] (U : Opens X) :
    Epi (S.g.hom.app (op U)) := by
  refine (AddCommGrpCat.epi_iff_surjective _).mpr (fun s ↦ ?_)
  obtain ⟨t, ht⟩ := exists_maximal_of_chains_bounded
    (flasque_under_chains_bounded S.g s)
    (fun ⟨f⟩ ⟨g⟩ ↦ ⟨g ≫ f⟩)
  have tle : t.right.1.unop ≤ U := leOfHom t.hom.1.unop
  have tcomp : s |_ t.right.1.unop = S.g.hom.app t.right.1 t.right.2 :=
    t.hom.map_val
  have : U ≤ t.right.1.unop := by
    intro x hx
    have hloc : CategoryTheory.Sheaf.IsLocallySurjective S.g :=
      (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
        (J := Opens.grothendieckTopology X) (A := AddCommGrpCat.{max u r})
        (φ := S.g)).mpr hS.epi_g
    let _ : CategoryTheory.Presheaf.IsLocallySurjective
        (Opens.grothendieckTopology X) S.g.hom := hloc
    have himage := CategoryTheory.Presheaf.imageSieve_mem
      (Opens.grothendieckTopology X) S.g.hom (U := op U) s
    obtain ⟨J, cover, hle, harrow, hsup⟩ :=
      exists_opens_cover_of_mem_grothendieckTopology U
        (CategoryTheory.Presheaf.imageSieve S.g.hom s) himage
    have hx' : x ∈ ⨆ j, cover j := by rw [hsup]; exact hx
    obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hx'
    let W := cover j
    have Wle : W ≤ U := hle j
    have hW : x ∈ W := hxj
    obtain ⟨t₁, ht₁⟩ := harrow j
    change (S.g.hom.app (op W)) t₁ = S.X₃.obj.map (homOfLE Wle).op s at ht₁
    have ht₁r : (S.g.hom.app (op W)) t₁ = s |_ W := by
      change (S.g.hom.app (op W)) t₁ = S.X₃.obj.map (homOfLE Wle).op s
      rw [show S.X₃.obj.map (homOfLE Wle).op s = s |_ W by rfl]
      exact ht₁
    let t₂ := t.right.2 |_ (t.right.1.unop ⊓ W) - t₁ |_ (t.right.1.unop ⊓ W)
    have ht₂ : (S.g.hom.app (op (t.right.1.unop ⊓ W))) t₂ = 0 := by
      have hA : (S.g.hom.app (op (t.right.1.unop ⊓ W)))
          (t.right.2 |_ (t.right.1.unop ⊓ W)) = s |_ (t.right.1.unop ⊓ W) := by
        simp [map_restrict, ← tcomp, restrict_restrict]
      have hB : (S.g.hom.app (op (t.right.1.unop ⊓ W)))
          (t₁ |_ (t.right.1.unop ⊓ W)) = s |_ (t.right.1.unop ⊓ W) := by
        rw [map_restrict, ht₁r, restrict_restrict]
      dsimp [t₂]
      rw [map_sub, hA, hB]
      exact sub_self _
    let P := TopCat.Sheaf.forget (AddCommGrpCat.{max u r}) X
    have : Limits.PreservesFiniteLimits P := by
      change Limits.PreservesFiniteLimits
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u r})
      infer_instance
    have hleft : (S.map P).Exact :=
      (((Functor.preservesFiniteLimits_tfae P).out 2 4 rfl rfl).mpr
        inferInstance S ⟨hS.exact, hS.mono_f⟩).1
    let E := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u r}).obj
      (op (t.right.1.unop ⊓ W))
    have : E.Additive := by unfold E; infer_instance
    have ht₃ : ∃ a : S.X₁.obj.obj (op (t.right.1.unop ⊓ W)),
        S.f.hom.app (op (t.right.1.unop ⊓ W)) a = t₂ :=
      (ShortComplex.ab_exact_iff ((S.map P).map E)).mp
        (((Functor.exact_tfae E).out 2 4 rfl rfl).mpr
          ⟨inferInstance, inferInstance⟩ (S.map P) hleft) _ ht₂
    obtain ⟨t₃, ht₃⟩ := ht₃
    obtain ⟨t₄, ht₄⟩ := (AddCommGrpCat.epi_iff_surjective
      (S.X₁.obj.map (homOfLE inf_le_right).op)).mp inferInstance t₃
    let f : Fin 2 → Opens X := ![t.right.1.unop, W]
    let sf : (i : Fin 2) → S.X₂.obj.obj (op (f i))
      | 0 => t.right.2
      | 1 => t₁ + (S.f.hom.app (op W)) t₄
    have hmap : ((S.f.hom.app (op W)) t₄) |_
        (t.right.1.unop ⊓ W) = t₂ := by
      rw [← TopCat.Presheaf.map_restrict S.f.hom inf_le_right t₄]
      change (S.f.hom.app (op (t.right.1.unop ⊓ W)))
        ((S.X₁.obj.map (homOfLE inf_le_right).op) t₄) = t₂
      rw [ht₄, ht₃]
    have hglue : sf 0 |_ (t.right.1.unop ⊓ W) = sf 1 |_ (t.right.1.unop ⊓ W) := by
      dsimp [sf, f]
      rw [restrict_sum, hmap]
      dsimp [t₂]
      simp only [add_sub_cancel]
    obtain ⟨t₅, ht₅, _⟩ : ∃! t₅, IsGluing S.X₂.obj f sf t₅ := by
      apply Sheaf.existsUnique_gluing
      simp only [IsCompatible, Fin.forall_fin_two]
      have hcomm : f 1 ⊓ f 0 ≤ t.right.1.unop ⊓ W := by
        simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one]
        exact le_of_eq (inf_comm _ _)
      refine ⟨⟨rfl, hglue⟩, Eq.symm ?_, rfl⟩
      -- `rw [restrict_restrict]` refuses here: the opens `f 1 ⊓ f 0` and
      -- `t.right.1.unop ⊓ W` are equal but differently presented, so the rewrite is done in
      -- term mode, where the equality is checked at default transparency.
      have e0 := TopCat.Presheaf.restrict_restrict (F := S.X₂.obj) hcomm
        (show t.right.1.unop ⊓ W ≤ f 0 from by
          simp only [f, Matrix.cons_val_zero]; exact inf_le_left) (sf 0)
      have e1 := TopCat.Presheaf.restrict_restrict (F := S.X₂.obj) hcomm
        (show t.right.1.unop ⊓ W ≤ f 1 from by
          simp only [f, Matrix.cons_val_one]; exact inf_le_right) (sf 1)
      exact e0.symm.trans
        ((congrArg (fun z ↦ restrictOpen z (f 1 ⊓ f 0) hcomm) hglue).trans e1)
    have hle : iSup f ≤ U := iSup_le_iff.mpr (Fin.forall_fin_two.mpr ⟨tle, Wle⟩)
    let t₆ : FlasqueUnder S.g s :=
      StructuredArrow.mk (S := Functor.elementsMk _ _ s)
        (T := (Functor.whiskerRight S.g.hom
          (CategoryTheory.forget AddCommGrpCat.{max u r})).mapElements)
        (Y := Functor.elementsMk _ _ t₅) <| Functor.Elements.homMk (homOfLE hle).op (by
          refine (eq_app_of_locally_eq ht₅ (by rw [Fin.forall_fin_two]; exact ⟨tle, Wle⟩) ?_).symm
          rw [Fin.forall_fin_two]
          refine ⟨tcomp.symm, ?_⟩
          -- Evaluating the zero composite of the short complex at `W`; done by applying the
          -- additive evaluation functor, since the rewrite route needs the morphisms of the
          -- sheaf category and of its underlying induced category to be one spelling.
          have hfg : (S.f.hom.app (op W) ≫ S.g.hom.app (op W)) = 0 := by
            let EW := (sheafSections (Opens.grothendieckTopology X)
              AddCommGrpCat.{max u r}).obj (op W)
            have h : EW.map S.f ≫ EW.map S.g = 0 :=
              (EW.map_comp S.f S.g).symm.trans
                ((congrArg EW.map S.zero).trans (EW.map_zero _ _))
            exact h
          have hrestr : s |_ W = S.X₃.obj.map (homOfLE Wle).op s := by rfl
          have hw : (S.g.hom.app (op W))
              (t₁ + (S.f.hom.app (op W)) t₄) =
                S.X₃.obj.map (homOfLE Wle).op s := by
            rw [map_add, ← CategoryTheory.comp_apply, hfg]
            rw [ht₁r]
            have hzero : (ConcreteCategory.hom
                (0 : S.X₁.obj.obj (op W) ⟶ S.X₃.obj.obj (op W))) t₄ = 0 := by rfl
            rw [hzero, add_zero]
            exact hrestr
          change (S.g.hom.app (op W))
            (t₁ + (S.f.hom.app (op W)) t₄) = S.X₃.obj.map (homOfLE Wle).op s
          exact hw)
    have ht₆ : Nonempty (t₆ ⟶ t) :=
      ⟨StructuredArrow.homMk (Functor.Elements.homMk (homOfLE (le_iSup f 0)).op (ht₅ 0))
        (by cat_disch)⟩
    exact leOfHom ((ht t₆) ht₆).some.right.1.unop ((le_iSup f 1) hW)
  exact ⟨t.right.2 |_ U, by simp [map_restrict, ← tcomp, restrict_restrict]⟩

/-- The quotient in a short exact sequence of abelian sheaves whose first two terms are flasque
is flasque. -/
private theorem flasque_quotient_generic {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{max u r} X)}
    [HasLimitsOfSize.{u, u} AddCommGrpCat.{max u r}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u r}]
    (hS : S.ShortExact) [S.X₁.IsFlasque] [S.X₂.IsFlasque] : S.X₃.IsFlasque := by
  constructor
  intro U V i
  have h₁ : Epi (S.g.hom.app U ≫ S.X₃.obj.map i) := by
    rw [← S.g.hom.naturality i]
    exact CategoryTheory.epi_comp' inferInstance
      (epi_of_shortExact_generic.{u, r} (X := X) hS V.unop)
  exact CategoryTheory.epi_of_epi (S.g.hom.app U) (S.X₃.obj.map i)

/-- Sheaves of modules whose underlying abelian sheaf is flasque. -/
private noncomputable abbrev flasqueProperty {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}) :
    ObjectProperty (SheafOfModules.{max u v} R) :=
  fun M => (highUnderlyingSheaf M).IsFlasque

/-- Every sheaf of modules embeds into one with flasque underlying abelian sheaf, namely into an
injective one. -/
private theorem flasqueProperty_exists_mono {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
    [EnoughInjectives (SheafOfModules.{max u v} R)]
    (M : SheafOfModules.{max u v} R) :
    ∃ N, ∃ (_ : flasqueProperty R N), ∃ f : M ⟶ N, Mono f := by
  obtain ⟨p⟩ := EnoughInjectives.presentation M
  let _ := p.injective
  exact ⟨p.J, highInjective_underlying_isFlasque p.J, p.f, p.mono⟩

/-- The class of sheaves of modules with flasque underlying abelian sheaf satisfies the
two-out-of-three property for short exact sequences and keeps sections over an open exact. -/
private theorem flasqueProperty_shortExact {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}) (U : Opens X)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    [HasLimitsOfSize.{u, u} AddCommGrpCat.{max u v}]
    (S : ShortComplex (SheafOfModules.{max u v} R)) (hS : S.ShortExact)
    (h₁ : flasqueProperty R S.X₁) (h₂ : flasqueProperty R S.X₂) :
    flasqueProperty R S.X₃ ∧
      (S.map (SheafOfModules.toSheaf R ⋙
        (sheafSections (Opens.grothendieckTopology X)
          AddCommGrpCat.{max u v}).obj (op U))).ShortExact := by
  let G : SheafOfModules.{max u v} R ⥤ AddCommGrpCat.{max u v} :=
    SheafOfModules.toSheaf R ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (op U)
  let T : SheafOfModules.{max u v} R ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} :=
    SheafOfModules.toSheaf R
  let Ttop : SheafOfModules.{max u v} R ⥤
      TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X) := T
  have : Ttop.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have : Limits.PreservesFiniteLimits Ttop := inferInstanceAs (Limits.PreservesFiniteLimits T)
  have : Limits.PreservesFiniteColimits Ttop :=
    inferInstanceAs (Limits.PreservesFiniteColimits T)
  let S' : ShortComplex (TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X)) := S.map Ttop
  have hS' : S'.ShortExact := hS.map_of_exact Ttop
  let _ : S'.X₁.IsFlasque := h₁
  let _ : S'.X₂.IsFlasque := h₂
  have h₃ : S'.X₃.IsFlasque := flasque_quotient_generic.{u, v} (X := TopCat.of X) hS'
  refine ⟨h₃, ?_⟩
  have : Limits.PreservesFiniteLimits
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (op U)) := by
    rw [show (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
      (op U) = sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op U) from rfl]
    infer_instance
  have hGlim : Limits.PreservesFiniteLimits G := by dsimp only [G]; infer_instance
  have hMap := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono G).mp hGlim S hS
  have hepi : Epi (S'.g.hom.app (op U)) :=
    epi_of_shortExact_generic.{u, v} (X := TopCat.of X) hS' U
  exact { exact := hMap.1, mono_f := hMap.2, epi_g := hepi }

/-- An exact functor commutes with the degreewise homology of a complex. -/
private noncomputable def mapHomologyIsoNat
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {ι : Type*} (c : ComplexShape ι) (n : ι) :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor B c n ≅
      HomologicalComplex.homologyFunctor A c n ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso F) (fun φ =>
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor A c n).map φ) F)

/-! ### Tag 01EV -/

/-! #### The Čech complex under a universe lift of the index type

`hF` quantifies over index types in `Type (max u v)` while the index type of a cover of a space
in `Type u` lies in `Type u`, so the Čech complex has to be reindexed along `ULift`. The
comparison is built by hand on the products. It cannot be obtained functorially: the index type's
universe is a parameter of `FormalCoproduct.{w}`, so `FormalCoproduct.mk I U` and
`FormalCoproduct.mk (ULift.{v} I) _` are objects of two *different* categories
(`FormalCoproduct.{u}` and `FormalCoproduct.{max u v}`) and no isomorphism between them exists.

The two morphisms are named rather than written inline, and each carries a `π` lemma proved by
`Pi.lift_π` with no expected type, hence in one spelling. Inline `let`s leave the goal with
unreduced projections, and the factor families of the two products are definitionally but not
syntactically equal, so an unprepared `rw`/`simp` matches nothing -- `rw [Category.assoc]` is
refused even on a visible `(f ≫ g) ≫ h`. -/

/-- Reindexing a product over `Fin (n + 1) → I` to one over `Fin (n + 1) → ULift I`. -/
private noncomputable def cechUliftHom {X : Type u} {I : Type u} [TopologicalSpace X]
    (U : I → Opens X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) (a : SimplexCategory) :
    (∏ᶜ fun i : ToType a → I => P.obj (op (∏ᶜ U ∘ i))) ⟶
      (∏ᶜ fun i : ToType a → ULift.{v} I =>
        P.obj (op (∏ᶜ (fun j : ULift.{v} I => U j.down) ∘ i))) :=
  Pi.lift (fun s => Pi.π _ (fun j => (s j).down))

/-- Reindexing a product over `Fin (n + 1) → ULift I` back to one over `Fin (n + 1) → I`. -/
private noncomputable def cechUliftInv {X : Type u} {I : Type u} [TopologicalSpace X]
    (U : I → Opens X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) (a : SimplexCategory) :
    (∏ᶜ fun i : ToType a → ULift.{v} I =>
        P.obj (op (∏ᶜ (fun j : ULift.{v} I => U j.down) ∘ i))) ⟶
      (∏ᶜ fun i : ToType a → I => P.obj (op (∏ᶜ U ∘ i))) :=
  Pi.lift (fun t => Pi.π _ (fun j => ULift.up (t j)))

@[reassoc (attr := simp)]
private lemma cechUliftHom_π {X : Type u} {I : Type u} [TopologicalSpace X]
    (U : I → Opens X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) (a : SimplexCategory)
    (s : ToType a → ULift.{v} I) :
    cechUliftHom U P a ≫
        Pi.π (fun i : ToType a → ULift.{v} I =>
          P.obj (op (∏ᶜ (fun j : ULift.{v} I => U j.down) ∘ i))) s =
      Pi.π (fun i : ToType a → I => P.obj (op (∏ᶜ U ∘ i))) (fun j => (s j).down) :=
  Pi.lift_comp_π _ _

@[reassoc (attr := simp)]
private lemma cechUliftInv_π {X : Type u} {I : Type u} [TopologicalSpace X]
    (U : I → Opens X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) (a : SimplexCategory)
    (t : ToType a → I) :
    cechUliftInv U P a ≫ Pi.π (fun i : ToType a → I => P.obj (op (∏ᶜ U ∘ i))) t =
      Pi.π (fun i : ToType a → ULift.{v} I =>
        P.obj (op (∏ᶜ (fun j : ULift.{v} I => U j.down) ∘ i))) (fun j => ULift.up (t j)) :=
  Pi.lift_comp_π _ _

/-- The cosimplicial structure map of a Čech object, in product form. -/
private noncomputable def cechMap {X : Type u} {I : Type r} [TopologicalSpace X]
    [UnivLE.{r, max u v}] (U : I → Opens X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {a b : SimplexCategory} (f : a ⟶ b) :
    (∏ᶜ fun i : ToType a → I => P.obj (op (∏ᶜ U ∘ i))) ⟶
      (∏ᶜ fun i : ToType b → I => P.obj (op (∏ᶜ U ∘ i))) :=
  Pi.lift (fun i => Pi.π _ (i ∘ SimplexCategory.Hom.toOrderHom f) ≫
    P.map (Pi.lift (fun x => Pi.π (U ∘ i) (SimplexCategory.Hom.toOrderHom f x))).op)

@[reassoc (attr := simp)]
private lemma cechMap_π {X : Type u} {I : Type r} [TopologicalSpace X]
    [UnivLE.{r, max u v}] (U : I → Opens X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {a b : SimplexCategory} (f : a ⟶ b) (i : ToType b → I) :
    cechMap U P f ≫ Pi.π (fun i : ToType b → I => P.obj (op (∏ᶜ U ∘ i))) i =
      Pi.π (fun i : ToType a → I => P.obj (op (∏ᶜ U ∘ i)))
          (i ∘ SimplexCategory.Hom.toOrderHom f) ≫
        P.map (Pi.lift (fun x => Pi.π (U ∘ i) (SimplexCategory.Hom.toOrderHom f x))).op :=
  Pi.lift_comp_π _ _

/-- Reindexing along `ULift` commutes with the cosimplicial structure maps. -/
@[reassoc (attr := simp)]
private lemma cechUliftHom_cechMap {X : Type u} {I : Type u} [TopologicalSpace X]
    (U : I → Opens X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {a b : SimplexCategory} (f : a ⟶ b) :
    cechMap U P f ≫ cechUliftHom U P b =
      cechUliftHom U P a ≫ cechMap (fun j : ULift.{v} I => U j.down) P f := by
  refine Pi.hom_ext _ _ fun s => ?_
  simp
  rfl

/-- Reindexing a Čech cosimplicial object along the universe lift of its index type. -/
private noncomputable def cechCosimplicialUliftIso {X : Type u} {I : Type u}
    [TopologicalSpace X] (U : I → Opens X)
    (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    ((CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk I U).cech).obj P) ≅
      ((CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk (ULift.{v} I) (fun i => U i.down)).cech).obj P) := by
  refine NatIso.ofComponents
    (app := fun a => ⟨cechUliftHom U P a, cechUliftInv U P a,
      Pi.hom_ext _ _ (fun t =>
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => cechUliftHom U P a ≫ k) (cechUliftInv_π U P a t)).trans
            (cechUliftHom_π U P a (fun j => ULift.up (t j))))).trans
          (Category.id_comp _).symm),
      Pi.hom_ext _ _ (fun s =>
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => cechUliftInv U P a ≫ k) (cechUliftHom_π U P a s)).trans
            (cechUliftInv_π U P a (fun j => (s j).down)))).trans
          (Category.id_comp _).symm)⟩) ?_
  intro a b f
  exact cechUliftHom_cechMap U P f

/-! ### The abelian structure at the coefficient universe

The three conditions that make the right derived functor of sections on `SheafOfModules.{v} R`
expressible — sheafification of `AddCommGrpCat.{v}`-valued presheaves, its inverting exactly the
locally bijective morphisms, and injective resolutions — all hold for the site of opens of a
space in `Type u` as soon as the coefficient universe dominates the space universe. They are
supplied as instances rather than assumed, so that Tag 01EV below carries only the source's
own hypothesis — the vanishing of the positive Čech cohomology — and so that a consumer can
write its conclusion down at a prescribed coefficient universe. At `v = u`, the single universe
of the Stacks Project, Mathlib already supplies all three and `UnivLE.{u, u}` as well, so the
statement then has no instance argument whatsoever.
-/

/-- Presheaves of abelian groups at a coefficient universe above the space universe sheafify:
the site of opens of a space in `Type u` is essentially `v`-small. -/
instance hasSheafifyOpensUnivLE {X : Type u} [TopologicalSpace X] [UnivLE.{u, v}] :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v} :=
  hasSheafifyEssentiallySmallSite _ _

/-- That sheafification inverts exactly the locally bijective morphisms, again by essential
`v`-smallness of the site of opens. -/
instance wEqualsLocallyBijectiveOpensUnivLE {X : Type u} [TopologicalSpace X]
    [UnivLE.{u, v}] :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- **Sheaves of modules on a space in `Type u` have enough injectives in every coefficient
universe `v` above `u`**, hence injective resolutions and right derived functors. This is
`SheafOfModules.enoughInjectives_of_univLE` at the site of open sets: that theorem's three
`UnivLE` hypotheses are `UnivLE.{u, v}` for the objects of the site, `UnivLE.{u, v}` again for
its homs, which also live in `Type u`, and `UnivLE.{v, v}` for the rings. -/
@[sga "4½ Etat_0 6.2" "special case"]
instance enoughInjectivesSheafOfModulesUnivLE {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}) [UnivLE.{u, v}] :
    EnoughInjectives (SheafOfModules.{v} R) :=
  (SheafOfModules.enoughInjectives_of_univLE R : EnoughInjectives (SheafOfModules.{v} R))

/-- **Stacks Project, Tag 01EV.** If all positive-degree Čech cohomology of a sheaf
of modules vanishes, then every positive right-derived functor of sections vanishes. -/
@[stacks 01EV]
public theorem isZero_rightDerived_sections_of_isZero_cechHomology
    {X : Type u} [TopologicalSpace X] [UnivLE.{u, v}]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
    (F : SheafOfModules.{v} R)
    (hF : ∀ {I : Type (max u v)} (U : I → Opens X) (p : ℕ), 0 < p →
      IsZero (((cechComplexFunctor U).obj
        (F.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u, v})).homology p)) :
    ∀ (U : Opens X) (p : ℕ), 0 < p →
      IsZero ((((SheafOfModules.toSheaf R ⋙
        (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
          (op U)).rightDerived p).obj F)) := by
  intro U p hp
  -- Sheafification and local bijectivity at the lifted coefficient universe.
  let _ : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u v} _ _
  let _ : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u v} _
  let _ : IsGrothendieckAbelian.{max u v} (SheafOfModules.{max u v} R) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, u, v, 0}
      (Opens.grothendieckTopology X) R
  let _ : EnoughInjectives (SheafOfModules.{max u v} R) :=
    IsGrothendieckAbelian.enoughInjectives
  -- Every family of opens covers its supremum, so all covers and all opens may be taken.
  let L := liftSheafOfModulesFunctor R
  let F' := L.obj F
  let B : Set (Opens X) := Set.univ
  let Cov : Set (Stacks.Cohomology.Basis.OpenCover.{u} X) := Set.univ
  have hBasis : Opens.IsBasis B :=
    Opens.isBasis_iff_cover.mpr fun V => ⟨{V}, fun W _ => Set.mem_univ W, by simp⟩
  have hCovBasis : ∀ V ∈ Cov, V.carrier ∈ B ∧ (∀ i, V.obj i ∈ B) ∧
      ∀ (q : ℕ) (s : Fin (q + 1) → V.ι), (⨅ k, V.obj (s k)) ∈ B :=
    fun V _ => ⟨Set.mem_univ _, fun _ => Set.mem_univ _, fun _ _ => Set.mem_univ _⟩
  have hCovCofinal : ∀ V ∈ B, ∀ W : Stacks.Cohomology.Basis.OpenCover.{u} X, W.carrier = V →
      ∃ Z ∈ Cov, Z.carrier = V ∧ Z.Refines W :=
    fun V _ W hW => ⟨W, Set.mem_univ _, hW, ⟨rfl, fun i => ⟨i, le_rfl⟩⟩⟩
  -- The Čech hypothesis, transported to the lifted sheaf and to `Type u`-indexed covers.
  have hCech : ∀ V ∈ Cov, ∀ q : ℕ, 0 < q →
      Stacks.Cohomology.Basis.CechCohomologyIsZero R F' V q := by
    intro V _ q hq
    have eCech : (cechComplexFunctor V.obj).obj
        (F.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u, v}) ≅
        (cechComplexFunctor V.obj).obj
          ((SheafOfModules.toSheaf R ⋙
            sheafToPresheaf (Opens.grothendieckTopology X)
              AddCommGrpCat.{max u v}).obj F') :=
      (cechComplexFunctor V.obj).mapIso (liftUnderlyingPresheafIso F).symm
    have eHom := (HomologicalComplex.homologyFunctor AddCommGrpCat
      (ComplexShape.up ℕ) q).mapIso eCech
    let eIndexComplex :=
      (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{max u v}).mapIso
        (cechCosimplicialUliftIso V.obj
          (F.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u, v}))
    have eIndexHom := (HomologicalComplex.homologyFunctor AddCommGrpCat
      (ComplexShape.up ℕ) q).mapIso eIndexComplex
    have hSmallIndex : IsZero (((cechComplexFunctor V.obj).obj
        (F.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u, v})).homology q) := by
      change IsZero (((FormalCoproduct.cochainComplexFunctor
        ((FormalCoproduct.mk V.ι V.obj).cech)).obj
        (F.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u, v})).homology q)
      exact IsZero.of_iso (hF (I := ULift.{v} V.ι) (fun i => V.obj i.down) q hq) eIndexHom
    exact IsZero.of_iso hSmallIndex eHom
  -- Tag 01EW at the lifted universe.
  have hH := Stacks.Cohomology.BasisCycles.isZero_hgroup_of_cech_isZero_on_basis
    R F' B hBasis Cov hCovBasis hCovCofinal hCech U (Set.mem_univ _) p hp
  -- The two functors of sections, and the comparison between them across the lift.
  let Glo : SheafOfModules.{v} R ⥤ AddCommGrpCat.{v} :=
    SheafOfModules.toSheaf R ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj (op U)
  let Ghi : SheafOfModules.{max u v} R ⥤ AddCommGrpCat.{max u v} :=
    SheafOfModules.toSheaf R ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (op U)
  let Ugr : AddCommGrpCat.{v} ⥤ AddCommGrpCat.{max u v} := AddCommGrpCat.uliftFunctor.{u, v}
  let α : L ⋙ Ghi ≅ Glo ⋙ Ugr :=
    NatIso.ofComponents (fun M => ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj
      (op U)).mapIso (liftUnderlyingPresheafIso M)) fun _ => by ext; rfl
  -- One complex computes both right derived functors: the lift of an injective resolution of `F`
  -- is a resolution of `F'` by sheaves with flasque underlying abelian sheaf.
  let Ires := injectiveResolution F
  let cshape := ComplexShape.up ℕ
  let K := (L.mapHomologicalComplex cshape).obj Ires.cocomplex
  let Jres := injectiveResolution F'
  let ε : (CochainComplex.single₀ (SheafOfModules.{max u v} R)).obj F' ⟶ K :=
    ((HomologicalComplex.singleMapHomologicalComplex L cshape 0).app F).inv ≫
      (L.mapHomologicalComplex cshape).map Ires.ι
  have hεq : QuasiIso ε := by
    have : QuasiIso ((L.mapHomologicalComplex cshape).map Ires.ι) := inferInstance
    exact quasiIso_comp _ _
  obtain ⟨β, hβ⟩ := CategoryTheory.InjectiveResolution.exists_desc_of_quasiIso
    (𝟙 F') Jres ε
  have hβ' : ε ≫ β = Jres.ι :=
    hβ.trans ((congrArg (fun k => k ≫ Jres.ι)
      ((CochainComplex.single₀ (SheafOfModules.{max u v} R)).map_id F')).trans
      (Category.id_comp _))
  let e1 := CategoryTheory.InjectiveResolution.isoRightDerivedObjOfQuasiIso Ghi
    (flasqueProperty R) (flasqueProperty_exists_mono R) (flasqueProperty_shortExact R U)
    Jres ε β hβ' (fun n => liftInjective_underlying_isFlasque (Ires.cocomplex.X n))
    (fun n => highInjective_underlying_isFlasque (Jres.cocomplex.X n)) p
  -- The same complex, read through `α`, computes the lift of the low-universe cohomology.
  let CL := (Glo.mapHomologicalComplex cshape).obj Ires.cocomplex
  let eC : (Ugr.mapHomologicalComplex cshape).obj CL ≅
      (Ghi.mapHomologicalComplex cshape).obj K :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (Glo ⋙ Ugr)) cshape).app
        Ires.cocomplex ≪≫
      (NatIso.mapHomologicalComplex α.symm cshape).app Ires.cocomplex ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ Ghi)) cshape).symm.app
        Ires.cocomplex
  let eAll : Ugr.obj ((Glo.rightDerived p).obj F) ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} cshape p).obj
        ((Ghi.mapHomologicalComplex cshape).obj K) :=
    Ugr.mapIso (Ires.isoRightDerivedObj Glo p) ≪≫
      ((mapHomologyIsoNat Ugr cshape p).app CL).symm ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} cshape p).mapIso eC
  have hHigh : IsZero ((Ghi.rightDerived p).obj F') := hH
  have hCarrier : Subsingleton (ULift.{u} ((Glo.rightDerived p).obj F)) :=
    AddCommGrpCat.subsingleton_of_isZero (IsZero.of_iso (IsZero.of_iso hHigh e1.symm) eAll)
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr
    ⟨fun a b => congrArg ULift.down (hCarrier.elim (ULift.up a) (ULift.up b))⟩

end Stacks.Cohomology.CechVanishing
