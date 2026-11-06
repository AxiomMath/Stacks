module

public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsSituation
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of modules as filtered colimits of finitely presented ones

Let `S` be a site with a distinguished collection of quasi-compact objects which covers it
(Stacks 0937). Over a sheaf of rings `R` on such a site, every sheaf of `R`-modules is a
filtered colimit of sheaves of modules admitting a *finite extension-by-zero presentation*:
a cokernel of a map between two finite direct sums of the sheaves `j_{U!} R|_U`, with `U`
running over distinguished objects.

The proof is the one in the source, in three steps. First, the sheaves `j_{U!} R|_U` for `U`
distinguished generate: morphisms out of `j_{U!} R|_U` are sections over `U`
(`extensionUnitCoyonedaIso`), so the direct sum over all pairs `(U, s)` of a distinguished
object and a section of `F` over it maps onto `F`, and iterating once on the kernel writes `F`
as a cokernel of a map `g` between two such direct sums. Second, `U` quasi-compact makes
`j_{U!} R|_U` a compact object — this is where Stacks 0935 enters — so any map out of it into a
direct sum factors through a finite subsum, and hence `g` restricts to maps between finite
subsums. Third, the finite subsums of the source and target that are compatible with `g` form a
filtered poset, and the cokernels of those restrictions of `g` form a filtered diagram whose
colimit is the cokernel of `g`, that is `F`.

## Main definitions

* `Stacks.Sites.extensionByZeroUnitPresheaf`, `Stacks.Sites.extensionByZeroUnit`: the extension
  by zero `j_{U!} R|_U` of the restricted ring sheaf, built as the sheafification of the
  presheaf `V ↦ (V ⟶ U) →₀ R(V)`.
* `Stacks.Sites.HasFiniteExtensionByZeroPresentation`: having a finite presentation by
  extensions by zero of the restricted ring from distinguished objects.

## Main results

* `Stacks.Sites.exists_epi_coproduct_extensionByZeroUnit`: Stacks 093B (2), every sheaf of
  modules is a quotient of a direct sum of extensions by zero of the restricted structure sheaf
  at distinguished objects.
* `Stacks.Sites.isFilteredColimit_of_hasEnoughQuasiCompactObjects`: every sheaf of modules is a
  filtered colimit of sheaves of modules with a finite extension-by-zero presentation.

## Implementation notes

The ring sheaf need not be commutative. The site objects, site morphisms, rings, and module
sections have independent universes, and the module sections of the given sheaf are lifted by
`Stacks.SheafOfModules.moduleULift` into the universe `max u₁ v₁ w v` containing all four; the
colimit cocone has
that lifted copy as its point, and the comparison `moduleULiftSelfIso` identifies it with the
original sheaf whenever the sections already lie in that universe. The lift is needed because
the direct sums and the sheafifications below are taken in a universe large enough for the
site, and imposes no size assumption on the sheaf being presented.

The extension by zero is built by hand, as the sheafification of `V ↦ (V ⟶ U) →₀ R(V)` with
coefficients transported by restriction, rather than as a pullback along `Over.forget U`: this
is the direct-sum description of `j_{U!} R|_U` from Stacks 03DI, and it avoids the
equal-universe restriction carried by Mathlib's automatic pullback-adjoint instance.

Several of the definitions involved are semireducible, so the definitional comparisons the
proofs rely on — the carrier of a module with restricted scalars, the sections of the lifted
presheaf, the vertex of `finiteSubcoproductsCocone` — do not go through at instance
transparency. They are made reducible locally with `attribute [local implicit_reducible]`,
which is how `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatColimits.lean` handles the
same obstruction and changes no elaboration option.

The two universe-lifting instances `HasSheafify J AddCommGrpCat.{t}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{t}` are `local instance`s rather than hypotheses:
they hold for every site that is small in the enlarged value universe, which the `UnivLE`
assumptions express, so they add nothing to the statement.

## References

* [Stacks Project, Tag 093B](https://stacks.math.columbia.edu/tag/093B)
* [Stacks Project, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
* [Stacks Project, Equation 18.30.7.2, Tag 093D](https://stacks.math.columbia.edu/tag/093D)
* [Stacks Project, Tag 0937](https://stacks.math.columbia.edu/tag/0937)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites

attribute [local implicit_reducible] ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  CoproductsFromFiniteFiltered.liftToFinsetObj
  CoproductsFromFiniteFiltered.finiteSubcoproductsCocone
  PresheafOfModules.presheaf PresheafOfModules.ofPresheaf
  AddCommGrpCat.uliftFunctor

open _root_.Stacks.SheafOfModules (presheafULift moduleULift moduleULiftFullyFaithful)

universe u₁ v₁ w v t

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- Before sheafification, extension by zero of the restricted unit has a copy of `R(V)`
for each arrow `V ⟶ U`. Restriction composes the arrows and restricts the coefficients. -/
noncomputable def extensionByZeroUnitPresheaf (R : Sheaf J RingCat.{w}) (U : C) :
    PresheafOfModules.{max v₁ w} R.obj := by
  let P : Cᵒᵖ ⥤ AddCommGrpCat.{max v₁ w} :=
    { obj := fun X => AddCommGrpCat.of ((X.unop ⟶ U) →₀ R.obj.obj X)
      map := fun {X Y} f => AddCommGrpCat.ofHom
        ((Finsupp.mapDomain.addMonoidHom (fun h => f.unop ≫ h)).comp
          (Finsupp.mapRange.addMonoidHom (R.obj.map f).hom.toAddMonoidHom))
      map_id := fun X => by
        apply AddCommGrpCat.hom_ext
        apply Finsupp.addHom_ext
        intro h r
        simp
      map_comp := fun f g => by
        apply AddCommGrpCat.hom_ext
        apply Finsupp.addHom_ext
        intro h r
        simp [Category.assoc] }
  letI : ∀ X, Module (R.obj.obj X) (P.obj X) := fun X => inferInstanceAs
    (Module (R.obj.obj X) ((X.unop ⟶ U) →₀ R.obj.obj X))
  exact PresheafOfModules.ofPresheaf P (fun {X Y} f r x => by
    change Finsupp.mapDomain _
        (Finsupp.mapRange (R.obj.map f) (map_zero (R.obj.map f).hom) (r • x)) =
      R.obj.map f r • Finsupp.mapDomain _
        (Finsupp.mapRange (R.obj.map f) (map_zero (R.obj.map f).hom) x)
    rw [Finsupp.mapRange_smul' r (R.obj.map f r) x
      (fun a => map_mul (R.obj.map f).hom r a), Finsupp.mapDomain_smul])

/-- If the objects and morphisms of `C` are `t`-small, then sheafification of presheaves of
abelian groups in `AddCommGrpCat.{t}` exists for `J`. -/
local instance (J : GrothendieckTopology C) [UnivLE.{u₁, t}] [UnivLE.{v₁, t}] :
    HasSheafify J AddCommGrpCat.{t} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{t, v₁, u₁} J

/-- If the objects and morphisms of `C` are `t`-small, then a morphism of presheaves of abelian
groups in `AddCommGrpCat.{t}` becomes an isomorphism after `J`-sheafification exactly when it is
locally bijective. -/
local instance (J : GrothendieckTopology C) [UnivLE.{u₁, t}] [UnivLE.{v₁, t}] :
    J.WEqualsLocallyBijective AddCommGrpCat.{t} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v₁, t, u₁, t + 1, t} J

/-- Presheaves of modules with values in `t` have coproducts indexed by `t`-small types. -/
local instance (R : Sheaf J RingCat.{w}) (K : Type t) :
    HasColimitsOfShape (Discrete K) (PresheafOfModules.{t} R.obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

/-- Sheaves of modules with values in `t` have coproducts indexed by `t`-small types. -/
local instance (R : Sheaf J RingCat.{w}) [UnivLE.{u₁, t}] [UnivLE.{v₁, t}] (K : Type t) :
    HasColimitsOfShape (Discrete K) (SheafOfModules.{t} R) :=
  @SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
    _ _ _ R _ _ _ _ (PresheafOfModules.hasColimitsOfShape _ _)

/-- Extension by zero of the restricted ring, with module values lifted into a universe
large enough for sheafification and the subsequent colimit constructions. -/
noncomputable def extensionByZeroUnit (R : Sheaf J RingCat.{w}) (U : C) :
    SheafOfModules.{max u₁ v₁ w v} R :=
  (PresheafOfModules.sheafification.{max u₁ v₁ w v} (𝟙 R.obj)).obj
    ((presheafULift.{max u₁ v₁ w v} R.obj).obj (extensionByZeroUnitPresheaf R U))

attribute [local implicit_reducible] presheafULift extensionByZeroUnitPresheaf
  extensionByZeroUnit

private noncomputable abbrev liftedUnitPresheaf (R : Sheaf J RingCat.{w}) (U : C) :=
  (presheafULift.{max u₁ v₁ w v} R.obj).obj (extensionByZeroUnitPresheaf R U)

private lemma liftedUnitPresheaf_map_single (R : Sheaf J RingCat.{w}) (U : C)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (h : X.unop ⟶ U) (r : R.obj.obj X) :
    (liftedUnitPresheaf.{u₁, v₁, w, v} R U).map f (ULift.up (Finsupp.single h r)) =
      ULift.up (Finsupp.single (f.unop ≫ h) (R.obj.map f r)) := by
  show ULift.up (Finsupp.mapDomain _
    (Finsupp.mapRange (R.obj.map f) (map_zero (R.obj.map f).hom) (Finsupp.single h r))) = _
  simp

private noncomputable def liftedUnitDesc (R : Sheaf J RingCat.{w}) (U : C)
    (M : PresheafOfModules.{max u₁ v₁ w v} R.obj) (x : M.obj (op U)) :
    liftedUnitPresheaf.{u₁, v₁, w, v} R U ⟶ M where
  app X := by
    change ModuleCat.of (R.obj.obj X)
      (ULift.{max u₁ v₁ w v} ((X.unop ⟶ U) →₀ R.obj.obj X)) ⟶ M.obj X
    exact ModuleCat.ofHom
      ((Finsupp.linearCombination (R.obj.obj X) (fun h : X.unop ⟶ U => M.map h.op x)).comp
      ULift.moduleEquiv.toLinearMap)
  naturality {X Y} f := by
    ext ⟨l⟩
    change Finsupp.linearCombination (R.obj.obj Y) (fun h : Y.unop ⟶ U => M.map h.op x)
        (Finsupp.mapDomain (fun h => f.unop ≫ h)
          (Finsupp.mapRange (R.obj.map f) (map_zero (R.obj.map f).hom) l)) =
      M.map f (Finsupp.linearCombination (R.obj.obj X) (fun h : X.unop ⟶ U => M.map h.op x) l)
    induction l using Finsupp.induction with
    | zero => simp
    | single_add h r l hh hr ih =>
      simp only [Finsupp.mapRange_add (map_add (R.obj.map f).hom), Finsupp.mapDomain_add, map_add,
        Finsupp.mapRange_single, Finsupp.mapDomain_single, Finsupp.linearCombination_single]
      rw [ih, M.map_smul, ← M.map_comp_apply]
      rfl

private lemma liftedUnitDesc_single (R : Sheaf J RingCat.{w}) (U : C)
    (M : PresheafOfModules.{max u₁ v₁ w v} R.obj) (x : M.obj (op U))
    (X : Cᵒᵖ) (h : X.unop ⟶ U) (r : R.obj.obj X) :
    (liftedUnitDesc.{u₁, v₁, w, v} R U M x).app X (ULift.up (Finsupp.single h r)) =
      r • M.map h.op x := by
  show Finsupp.linearCombination (R.obj.obj X) (fun h : X.unop ⟶ U => M.map h.op x)
    (Finsupp.single h r) = _
  exact Finsupp.linearCombination_single ..

private noncomputable def liftedUnitHomEquiv (R : Sheaf J RingCat.{w}) (U : C)
    (M : PresheafOfModules.{max u₁ v₁ w v} R.obj) :
    (liftedUnitPresheaf.{u₁, v₁, w, v} R U ⟶ M) ≃ M.obj (op U) where
  toFun f := f.app (op U) (ULift.up (Finsupp.single (𝟙 U) 1))
  invFun := liftedUnitDesc.{u₁, v₁, w, v} R U M
  left_inv f := by
    let x := f.app (op U) (ULift.up (Finsupp.single (𝟙 U) 1))
    ext X ⟨l⟩
    induction l using Finsupp.induction with
    | zero =>
      exact (map_zero ((liftedUnitDesc.{u₁, v₁, w, v} R U M x).app X).hom).trans
        (map_zero (f.app X).hom).symm
    | single_add h r l hh hr ih =>
      have hs : (ULift.up (Finsupp.single h r) :
          (liftedUnitPresheaf.{u₁, v₁, w, v} R U).obj X) =
          r • (liftedUnitPresheaf.{u₁, v₁, w, v} R U).map h.op
            (ULift.up (Finsupp.single (𝟙 U) 1)) := by
        rw [liftedUnitPresheaf_map_single.{u₁, v₁, w, v}]
        apply ULift.ext
        change Finsupp.single h r = r • Finsupp.single (h ≫ 𝟙 U) (R.obj.map h.op 1)
        simp
      have hsingle : (liftedUnitDesc.{u₁, v₁, w, v} R U M x).app X
          (ULift.up (Finsupp.single h r)) = f.app X (ULift.up (Finsupp.single h r)) := by
        rw [liftedUnitDesc_single.{u₁, v₁, w, v}, hs, map_smul,
          PresheafOfModules.naturality_apply]
        rfl
      exact (map_add ((liftedUnitDesc.{u₁, v₁, w, v} R U M x).app X).hom
        (ULift.up (Finsupp.single h r)) (ULift.up l)).trans
        ((congrArg₂ (· + ·) hsingle ih).trans
          (map_add (f.app X).hom (ULift.up (Finsupp.single h r)) (ULift.up l)).symm)
  right_inv x := by
    change (liftedUnitDesc.{u₁, v₁, w, v} R U M x).app (op U)
      (ULift.up (Finsupp.single (𝟙 U) 1)) = x
    rw [liftedUnitDesc_single.{u₁, v₁, w, v}, show ((𝟙 U : U ⟶ U).op) = 𝟙 (op U) from rfl,
      M.map_id]
    exact one_smul _ x

private noncomputable def extensionUnitHomEquiv (R : Sheaf J RingCat.{w}) (U : C)
    (M : SheafOfModules.{max u₁ v₁ w v} R) :
    (extensionByZeroUnit.{u₁, v₁, w, v} R U ⟶ M) ≃ M.val.obj (op U) :=
  ((PresheafOfModules.sheafificationAdjunction.{max u₁ v₁ w v} (𝟙 R.obj)).homEquiv _ M).trans
    (liftedUnitHomEquiv.{u₁, v₁, w, v} R U _)

private lemma extensionUnitHomEquiv_comp (R : Sheaf J RingCat.{w}) (U : C)
    {M N : SheafOfModules.{max u₁ v₁ w v} R}
    (f : extensionByZeroUnit.{u₁, v₁, w, v} R U ⟶ M) (g : M ⟶ N) :
    extensionUnitHomEquiv.{u₁, v₁, w, v} R U N (f ≫ g) =
      g.val.app (op U) (extensionUnitHomEquiv.{u₁, v₁, w, v} R U M f) :=
  congrArg (fun k => k.app (op U) (ULift.up (Finsupp.single (𝟙 U) 1)))
    ((PresheafOfModules.sheafificationAdjunction.{max u₁ v₁ w v}
      (𝟙 R.obj)).homEquiv_naturality_right f g)

private lemma extensionUnitHomEquiv_add (R : Sheaf J RingCat.{w}) (U : C)
    (M : SheafOfModules.{max u₁ v₁ w v} R)
    (f g : extensionByZeroUnit.{u₁, v₁, w, v} R U ⟶ M) :
    extensionUnitHomEquiv.{u₁, v₁, w, v} R U M (f + g) =
      extensionUnitHomEquiv.{u₁, v₁, w, v} R U M f +
        extensionUnitHomEquiv.{u₁, v₁, w, v} R U M g := by
  let adj := PresheafOfModules.sheafificationAdjunction.{max u₁ v₁ w v} (𝟙 R.obj)
  have h : adj.homEquiv _ M (f + g) = adj.homEquiv _ M f + adj.homEquiv _ M g := by
    simp only [Adjunction.homEquiv_unit, Functor.map_add, Preadditive.comp_add]
  exact congrArg (fun k => k.app (op U) (ULift.up (Finsupp.single (𝟙 U) 1))) h

/-- Morphisms out of `j_{U!} R|_U` are sections over `U`, naturally and additively. -/
private noncomputable def extensionUnitCoyonedaIso (R : Sheaf J RingCat.{w}) (U : C) :
    preadditiveCoyoneda.obj (op (extensionByZeroUnit.{u₁, v₁, w, v} R U)) ≅
      SheafOfModules.toSheaf.{max u₁ v₁ w v} R ⋙
        (sheafSections J AddCommGrpCat.{max u₁ v₁ w v}).obj (op U) :=
  NatIso.ofComponents
    (fun M => AddEquiv.toAddCommGrpIso
      { __ := extensionUnitHomEquiv.{u₁, v₁, w, v} R U M
        map_add' := extensionUnitHomEquiv_add.{u₁, v₁, w, v} R U M })
    (fun g => by
      ext f
      exact extensionUnitHomEquiv_comp.{u₁, v₁, w, v} R U f g)

/-- **Stacks Project, Tag 093B (2).** Every sheaf of `R`-modules is a quotient of a direct sum
`⊕ j_{U_i!} R|_{U_i}` of extensions by zero of the restricted structure sheaf at distinguished
objects: one summand for each pair of a distinguished object and a section of the module over
it. This is the generation step on which the presentations of Tag 093C rest. -/
@[stacks 093B "part (2), modules"]
theorem exists_epi_coproduct_extensionByZeroUnit
    (S : QuasiCompactObjectsSituation C) (hEnough : S.HasEnoughObjects)
    (R : Sheaf S.topology RingCat.{w}) (M : SheafOfModules.{max u₁ v₁ w v} R) :
    ∃ (A : Type (max u₁ v₁ w v)) (U : A → C), (∀ i, U i ∈ S.objects) ∧
      ∃ p : (∐ fun i => extensionByZeroUnit.{u₁, v₁, w, v} R (U i)) ⟶ M, Epi p := by
  let A := Σ U : {U : C // U ∈ S.objects}, M.val.obj (op U.1)
  let U : A → C := fun i => i.1.1
  let p : (∐ fun i : A => extensionByZeroUnit.{u₁, v₁, w, v} R (U i)) ⟶ M :=
    Sigma.desc fun i => (extensionUnitHomEquiv.{u₁, v₁, w, v} R (U i) M).symm i.2
  refine ⟨A, U, fun i => i.1.2, p, ⟨?_⟩⟩
  intro N f g h
  have hs (V : C) (hV : V ∈ S.objects) (x : M.val.obj (op V)) :
      f.val.app (op V) x = g.val.app (op V) x := by
    have hh := congrArg (fun k => Sigma.ι
      (fun i : A => extensionByZeroUnit.{u₁, v₁, w, v} R (U i)) ⟨⟨V, hV⟩, x⟩ ≫ k) h
    simp only [← Category.assoc, p, Sigma.ι_desc] at hh
    have he := congrArg (extensionUnitHomEquiv.{u₁, v₁, w, v} R V N) hh
    simpa only [U, extensionUnitHomEquiv_comp, Equiv.apply_symm_apply] using he
  apply (SheafOfModules.toSheaf R).map_injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext X
  obtain ⟨𝒰, h𝒰, hB⟩ := hEnough X.unop
  apply N.isSheaf.hom_ext_ofArrows 𝒰.f h𝒰
  intro i
  ext x
  exact (PresheafOfModules.naturality_apply f.val (𝒰.f i).op x).symm.trans
    ((hs _ (hB i) (M.val.map (𝒰.f i).op x)).trans
      (PresheafOfModules.naturality_apply g.val (𝒰.f i).op x))

/-- Compactness turns a morphism into a coproduct into one with finite support. -/
private lemma morphism_from_compact_object_factors_through_finite_subcoproduct
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [UnivLE.{u₁, t}] [UnivLE.{v₁, t}] [UnivLE.{w, t}]
    (X : SheafOfModules.{t} R) (A : Type t) (Y : A → SheafOfModules.{t} R)
    (hcompact : ∀ (ι : Type t),
      PreservesColimitsOfShape (Discrete ι) (preadditiveCoyoneda.obj (op X)))
    (f : X ⟶ ∐ Y) :
    ∃ (s : Finset (Discrete A))
      (g : X ⟶ ∐ fun a : s => Y a.1.as),
      g ≫ Sigma.desc (fun a : s => Sigma.ι Y a.1.as) = f := by
  let H : SheafOfModules.{t} R ⥤ AddCommGrpCat.{max t u₁} := preadditiveCoyoneda.obj (op X)
  let : PreservesColimitsOfShape (Discrete A) H := hcompact A
  let cB : Cocone (Discrete.functor Y) := Sigma.cocone (Discrete.functor Y)
  let hB : IsColimit cB := coproductIsCoproduct' (Discrete.functor Y)
  let hHB : IsColimit (H.mapCocone cB) := isColimitOfPreserves H hB
  let Z : A → AddCommGrpCat.{max t u₁} := fun a => H.obj (Y a)
  let FZ : Discrete A ⥤ AddCommGrpCat.{max t u₁} := (Discrete.functor Y) ⋙ H
  let cZ : Cocone FZ := Sigma.cocone FZ
  let hZ : IsColimit cZ := coproductIsCoproduct' FZ
  let e : H.obj (∐ Y) ≅ ∐ Z := hHB.coconePointUniqueUpToIso hZ
  let : IsFiltered (Finset (Discrete A)) := inferInstance
  let : PreservesColimit
      (CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor Z))
      (forget AddCommGrpCat.{max t u₁}) := by
    let Ffin := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor Z)
    exact preservesColimit_of_preserves_colimit_cocone
      (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit.{t, u₁} Ffin)
      (CategoryTheory.Limits.Types.TypeMax.colimitCoconeIsColimit.{t, u₁}
        (Ffin ⋙ forget AddCommGrpCat.{max t u₁}))
  let hfin := CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone Z
  obtain ⟨s, y, hy⟩ := Concrete.isColimit_exists_rep
    (CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor Z)) hfin (e.hom f)
  let : PreservesColimitsOfShape (Discrete s) H := hcompact s
  let : HasColimit (Discrete.functor (fun a : s => Y a.1.as)) := inferInstance
  let FD := Discrete.functor (fun a : s => Y a.1.as)
  let α : H.obj (∐ fun a : s => Y a.1.as) ≅ ∐ fun a : s => Z a.1.as :=
    H.mapIso (Sigma.isoColimit FD) ≪≫ preservesColimitIso H FD ≪≫
      (Sigma.isoColimit (FD ⋙ H)).symm
  let g : X ⟶ ∐ fun a : s => Y a.1.as := α.inv y
  refine ⟨s, g, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance
  rw [← hy]
  have hcomp :
      H.map (Sigma.desc (fun a : s => Sigma.ι Y a.1.as)) ≫ e.hom =
        α.hom ≫ Sigma.desc (fun a : s => Sigma.ι Z a.1.as) := by
    let hc : IsColimit (H.mapCocone (Sigma.cocone FD)) :=
      isColimitOfPreserves H (coproductIsCoproduct' FD)
    apply hc.hom_ext
    intro a
    have hleft :
        H.map ((Sigma.cocone FD).ι.app a) ≫
          H.map (Sigma.desc (fun a : s => Sigma.ι Y a.1.as)) =
            H.map (Sigma.ι Y a.as.1.as) := by
      show H.map (Sigma.ι (fun j : s => Y j.1.as) a.as) ≫
        H.map (Sigma.desc (fun a : s => Sigma.ι Y a.1.as)) = _
      rw [← H.map_comp]
      congr 1
      exact Sigma.ι_desc _ _
    have hmiddle : H.map (Sigma.ι Y a.as.1.as) ≫ e.hom = Sigma.ι Z a.as.1.as :=
      IsColimit.comp_coconePointUniqueUpToIso_hom hHB hZ (Discrete.mk a.as.1.as)
    have hright :
        H.map ((Sigma.cocone FD).ι.app a) ≫ α.hom ≫
          Sigma.desc (fun a : s => Sigma.ι Z a.1.as) = Sigma.ι Z a.as.1.as := by
      show H.map (Sigma.ι (fun j : s => Y j.1.as) a.as) ≫ α.hom ≫
        Sigma.desc (fun a : s => Sigma.ι Z a.1.as) = _
      dsimp [α]
      have hi : Sigma.ι (fun j : s => Y j.1.as) a.as ≫
          (Sigma.isoColimit FD).hom = colimit.ι FD (Discrete.mk a.as) := by
        simpa [FD] using (Sigma.ι_isoColimit_hom FD a.as)
      rw [← Category.assoc, ← Category.assoc, ← H.map_comp, congrArg H.map hi, ← Category.assoc,
        ι_preservesColimitIso_hom, Sigma.ι_isoColimit_inv]
      exact Sigma.ι_desc _ _
    calc
      H.map ((Sigma.cocone FD).ι.app a) ≫
          H.map (Sigma.desc (fun a : s => Sigma.ι Y a.1.as)) ≫ e.hom =
        H.map (Sigma.ι Y a.as.1.as) ≫ e.hom := by rw [← Category.assoc, hleft]
      _ = Sigma.ι Z a.as.1.as := hmiddle
      _ = H.map ((Sigma.cocone FD).ι.app a) ≫ α.hom ≫
          Sigma.desc (fun a : s => Sigma.ι Z a.1.as) := hright.symm
  have hx := congrArg (fun k : H.obj (∐ fun a : s => Y a.1.as) ⟶ ∐ Z =>
    k (α.inv y)) hcomp
  simp only [ConcreteCategory.comp_apply] at hx
  have hmap : H.map (Sigma.desc (fun a : s => Sigma.ι Y a.1.as)) (α.inv y) =
      (α.inv y) ≫ Sigma.desc (fun a : s => Sigma.ι Y a.1.as) := rfl
  have hα : α.hom (α.inv y) = y := ConcreteCategory.congr_hom α.inv_hom_id y
  rw [hmap, hα] at hx
  show (ConcreteCategory.hom e.hom) (g ≫ Sigma.desc (fun a : s => Sigma.ι Y a.1.as)) =
    (ConcreteCategory.hom (Sigma.desc (fun a : s => Sigma.ι Z a.1.as))) y
  exact hx

private lemma finite_source_map_factors_through_finite_target
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [UnivLE.{u₁, t}] [UnivLE.{v₁, t}] [UnivLE.{w, t}]
    {A B : Type t} (X : A → SheafOfModules.{t} R) (Y : B → SheafOfModules.{t} R)
    (hcompact : ∀ a (ι : Type t),
      PreservesColimitsOfShape (Discrete ι) (preadditiveCoyoneda.obj (op (X a))))
    (g : (∐ X) ⟶ (∐ Y)) (s : Finset (Discrete A)) :
    ∃ (t : Finset (Discrete B))
      (f : (∐ fun a : s => X a.1.as) ⟶ (∐ fun b : t => Y b.1.as)),
      Sigma.desc (fun a : s => Sigma.ι X a.1.as) ≫ g =
        f ≫ Sigma.desc (fun b : t => Sigma.ι Y b.1.as) := by
  classical
  choose T q hq using fun a : s =>
    morphism_from_compact_object_factors_through_finite_subcoproduct
      (X a.1.as) B Y (hcompact a.1.as) (Sigma.ι X a.1.as ≫ g)
  let t : Finset (Discrete B) := Finset.univ.biUnion T
  let e (a : s) : (∐ fun b : T a => Y b.1.as) ⟶ (∐ fun b : t => Y b.1.as) :=
    Sigma.desc fun b => Sigma.ι (fun b : t => Y b.1.as)
      ⟨b.1, Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, b.2⟩⟩
  have he (a : s) : e a ≫ Sigma.desc (fun b : t => Sigma.ι Y b.1.as) =
      Sigma.desc (fun b : T a => Sigma.ι Y b.1.as) := by
    apply Sigma.hom_ext
    intro b
    simp [e]
  let f : (∐ fun a : s => X a.1.as) ⟶ (∐ fun b : t => Y b.1.as) :=
    Sigma.desc fun a => q a ≫ e a
  refine ⟨t, f, ?_⟩
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, Sigma.ι_desc, ← hq, ← he]
  simp [f]

section FiniteCokernels

universe d a
variable {E : Type d} [Category.{a} E] [HasZeroMorphisms E]
  [HasColimitsOfSize.{a, a} E]

open CoproductsFromFiniteFiltered

private lemma finiteSubcoproduct_mono {A : Type a} (X : A → E)
    (s : Finset (Discrete A)) :
    Mono ((finiteSubcoproductsCocone X).ι.app s) := by
  classical
  let r : (∐ X) ⟶ (∐ fun i : s => X i.1.as) :=
    Sigma.desc fun i => if h : Discrete.mk i ∈ s then
      Sigma.ι (fun i : s => X i.1.as) ⟨Discrete.mk i, h⟩ else 0
  have hr : (finiteSubcoproductsCocone X).ι.app s ≫ r = 𝟙 _ := by
    apply Sigma.hom_ext
    intro i
    show Sigma.ι (fun j : s => X j.1.as) i ≫
        Sigma.desc (fun j : s => Sigma.ι X j.1.as) ≫ r =
      Sigma.ι (fun j : s => X j.1.as) i ≫ 𝟙 (∐ fun j : s => X j.1.as)
    simp [r, i.2]
  exact SplitMono.mono ⟨r, hr⟩

private lemma exists_filtered_finite_cokernels
    {A B : Type a} (X : A → E) (Y : B → E) (g : (∐ X) ⟶ (∐ Y))
    (hfin : ∀ s : Finset (Discrete A), ∃ t : Finset (Discrete B),
      ∃ f : (liftToFinsetObj (Discrete.functor X)).obj s ⟶
        (liftToFinsetObj (Discrete.functor Y)).obj t,
      (finiteSubcoproductsCocone X).ι.app s ≫ g =
        f ≫ (finiteSubcoproductsCocone Y).ι.app t) :
    ∃ (I : Type a) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ E) (c : Cocone D), c.pt = cokernel g ∧ Nonempty (IsColimit c) ∧
        ∀ i, ∃ (s : Finset (Discrete A)) (t : Finset (Discrete B))
          (f : (∐ fun j : s => X j.1.as) ⟶ (∐ fun j : t => Y j.1.as)),
          Nonempty (D.obj i ≅ cokernel f) := by
  classical
  let FX := liftToFinsetObj (Discrete.functor X)
  let FY := liftToFinsetObj (Discrete.functor Y)
  let cX := finiteSubcoproductsCocone X
  let cY := finiteSubcoproductsCocone Y
  let I := {p : Finset (Discrete A) × Finset (Discrete B) //
    ∃ f : FX.obj p.1 ⟶ FY.obj p.2, cX.ι.app p.1 ≫ g = f ≫ cY.ι.app p.2}
  have hex (s : Finset (Discrete A)) (t : Finset (Discrete B)) :
      ∃ i : I, s ⊆ i.1.1 ∧ t ⊆ i.1.2 := by
    obtain ⟨t', f, hf⟩ := hfin s
    refine ⟨⟨(s, t ∪ t'), f ≫ FY.map (homOfLE Finset.subset_union_right), ?_⟩,
      le_rfl, Finset.subset_union_left⟩
    rw [Category.assoc, cY.w (homOfLE (Finset.subset_union_right : t' ⊆ t ∪ t'))]
    exact hf
  have : Nonempty I := ⟨(hex ∅ ∅).choose⟩
  have : IsDirectedOrder I := ⟨fun i j => by
    obtain ⟨k, hk₁, hk₂⟩ := hex (i.1.1 ∪ j.1.1) (i.1.2 ∪ j.1.2)
    exact ⟨k, ⟨Finset.subset_union_left.trans hk₁, Finset.subset_union_left.trans hk₂⟩,
      ⟨Finset.subset_union_right.trans hk₁, Finset.subset_union_right.trans hk₂⟩⟩⟩
  have hmX : Monotone (fun i : I => i.1.1) := fun _ _ h => h.1
  have hmY : Monotone (fun i : I => i.1.2) := fun _ _ h => h.2
  let pX : I ⥤ Finset (Discrete A) := hmX.functor
  let pY : I ⥤ Finset (Discrete B) := hmY.functor
  have : pX.Final := hmX.final_functor_iff.2 fun s => (hex s ∅).imp fun i hi => hi.1
  have : pY.Final := hmY.final_functor_iff.2 fun t => (hex ∅ t).imp fun i hi => hi.2
  let L := pX ⋙ FX
  let N := pY ⋙ FY
  let l : Cocone L := cX.whisker pX
  let n : Cocone N := cY.whisker pY
  let hl : IsColimit l := (Functor.Final.isColimitWhiskerEquiv pX cX).symm
    (isColimitFiniteSubproductsCocone X)
  let hn : IsColimit n := (Functor.Final.isColimitWhiskerEquiv pY cY).symm
    (isColimitFiniteSubproductsCocone Y)
  let f (i : I) : L.obj i ⟶ N.obj i := i.2.choose
  have hf (i : I) : l.ι.app i ≫ g = f i ≫ n.ι.app i := i.2.choose_spec
  have hw {i j : I} (h : i ⟶ j) : L.map h ≫ f j = f i ≫ N.map h := by
    have : Mono (n.ι.app j) := finiteSubcoproduct_mono Y j.1.2
    apply (cancel_mono (n.ι.app j)).1
    calc
      (L.map h ≫ f j) ≫ n.ι.app j = L.map h ≫ (l.ι.app j ≫ g) := by
        rw [Category.assoc, hf]
      _ = l.ι.app i ≫ g := by rw [← Category.assoc, l.w]
      _ = f i ≫ n.ι.app i := hf i
      _ = (f i ≫ N.map h) ≫ n.ι.app j := by rw [Category.assoc, n.w]
  let D : I ⥤ E :=
    { obj i := cokernel (f i)
      map h := cokernel.map _ _ (L.map h) (N.map h) (hw h).symm
      map_id i := by
        apply coequalizer.hom_ext
        simp
      map_comp h k := by
        apply coequalizer.hom_ext
        simp [Category.assoc] }
  let π : N ⟶ D :=
    { app i := cokernel.π (f i)
      naturality i j h := by simp [D] }
  let c : Cocone D :=
    { pt := cokernel g
      ι :=
        { app i := cokernel.desc (f i) (n.ι.app i ≫ cokernel.π g) (by
            rw [← Category.assoc, ← hf, Category.assoc, cokernel.condition, comp_zero])
          naturality i j h := by
            apply coequalizer.hom_ext
            simp [D, Category.assoc] } }
  have hc : IsColimit c := by
    let liftCocone (s : Cocone D) : Cocone N :=
      { pt := s.pt
        ι := π ≫ s.ι }
    have kill (s : Cocone D) : g ≫ hn.desc (liftCocone s) = 0 := by
      apply hl.hom_ext
      intro i
      rw [← Category.assoc, hf, Category.assoc, hn.fac]
      simp [liftCocone, π]
    refine
      { desc := fun s => cokernel.desc g (hn.desc (liftCocone s)) (kill s)
        fac := fun s i => ?_
        uniq := fun s m hm => ?_ }
    · apply coequalizer.hom_ext
      simp only [Category.assoc, c, cokernel.π_desc_assoc, cokernel.π_desc]
      exact hn.fac (liftCocone s) i
    · apply coequalizer.hom_ext
      rw [cokernel.π_desc]
      apply hn.hom_ext
      intro i
      rw [hn.fac]
      show n.ι.app i ≫ cokernel.π g ≫ m = cokernel.π (f i) ≫ s.ι.app i
      calc
        n.ι.app i ≫ cokernel.π g ≫ m = cokernel.π (f i) ≫ c.ι.app i ≫ m := by
          rw [← Category.assoc, ← Category.assoc]
          congr 1
          exact (cokernel.π_desc _ _ _).symm
        _ = _ := by rw [hm]
  exact ⟨I, inferInstance, inferInstance, D, c, rfl, ⟨hc⟩,
    fun i => ⟨i.1.1, i.1.2, f i, ⟨Iso.refl _⟩⟩⟩

end FiniteCokernels

/-- A finite presentation as a cokernel between finite coproducts of extensions by zero
of the structure sheaf restricted to distinguished objects. All comparisons take place
after the canonical universe lift; no size assumption is imposed on `G`. -/
@[stacks 093D "the modules of Equation 18.30.7.2, after the canonical universe lift"]
def HasFiniteExtensionByZeroPresentation
    (S : QuasiCompactObjectsSituation C)
    (R : Sheaf S.topology RingCat.{w}) (G : SheafOfModules.{v} R) : Prop :=
  ∃ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
    (∀ i, U i ∈ S.objects) ∧ (∀ j, V j ∈ S.objects) ∧
      ∃ f : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, v} R (V j)) ⟶
          (∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, v} R (U i)),
        Nonempty (cokernel f ≅ (moduleULift.{max u₁ v₁ w v} R).obj G)

private noncomputable def moduleULiftSelfIso (R : Sheaf J RingCat.{w})
    (M : SheafOfModules.{max u₁ v₁ w v} R) :
    (moduleULift.{max u₁ v₁ w v} R).obj M ≅ M :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun X => by
      change ModuleCat.of (R.obj.obj X) (ULift.{max u₁ v₁ w v} (M.val.obj X)) ≅ M.val.obj X
      exact ULift.moduleEquiv.toModuleIso)
      (fun {X Y} f => by ext ⟨x⟩; rfl))

private lemma finitePresentation_of_cokernel_iso
    (S : QuasiCompactObjectsSituation C) (R : Sheaf S.topology RingCat.{w})
    {A B : Type (max u₁ v₁ w v)} [Finite A] [Finite B]
    (U : B → C) (V : A → C) (hU : ∀ i, U i ∈ S.objects) (hV : ∀ j, V j ∈ S.objects)
    (f : (∐ fun j => extensionByZeroUnit.{u₁, v₁, w, v} R (V j)) ⟶
      (∐ fun i => extensionByZeroUnit.{u₁, v₁, w, v} R (U i)))
    (G : SheafOfModules.{max u₁ v₁ w v} R) (e : cokernel f ≅ G) :
    HasFiniteExtensionByZeroPresentation S R G := by
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  let a := (Fintype.equivFin A).symm
  let b := (Fintype.equivFin B).symm
  let eA := Sigma.reindex a (fun j => extensionByZeroUnit.{u₁, v₁, w, v} R (V j))
  let eB := Sigma.reindex b (fun i => extensionByZeroUnit.{u₁, v₁, w, v} R (U i))
  refine ⟨Fintype.card B, Fintype.card A, U ∘ b, V ∘ a,
    fun i => hU _, fun j => hV _, eA.hom ≫ f ≫ eB.inv, ⟨?_⟩⟩
  exact cokernel.mapIso _ f eA eB
      (by rw [Category.assoc, Category.assoc, eB.inv_hom_id, Category.comp_id]) ≪≫ e ≪≫
    (moduleULiftSelfIso.{u₁, v₁, w, v} R G).symm

/-- **Stacks Project, Tag 093C (modules).** Every module sheaf is a filtered colimit
of finite cokernel presentations by extensions by zero from distinguished objects. -/
@[stacks 093C "modules"]
theorem isFilteredColimit_of_hasEnoughQuasiCompactObjects
    (S : QuasiCompactObjectsSituation C)
    (hEnough : S.HasEnoughObjects) (hqc : S.ObjectsAreQuasiCompact)
    (R : Sheaf S.topology RingCat.{w}) (F : SheafOfModules.{v} R) :
    ∃ (I : Type (max u₁ v₁ w v)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ SheafOfModules.{max u₁ v₁ w v} R)
      (ι : D ⟶ (Functor.const I).obj ((moduleULift.{max u₁ v₁ w v} R).obj F)),
      Nonempty (IsColimit (Cocone.mk ((moduleULift.{max u₁ v₁ w v} R).obj F) ι)) ∧
        ∀ i, HasFiniteExtensionByZeroPresentation S R (D.obj i) := by
  classical
  let F' := (moduleULift.{max u₁ v₁ w v} R).obj F
  obtain ⟨B, U, hU, p, hp⟩ := exists_epi_coproduct_extensionByZeroUnit.{u₁, v₁, w, v} S hEnough R F'
  let := hp
  obtain ⟨A, V, hV, q, hq⟩ :=
    exists_epi_coproduct_extensionByZeroUnit.{u₁, v₁, w, v} S hEnough R (kernel p)
  let := hq
  let g := q ≫ kernel.ι p
  let e : cokernel g ≅ F' := cokernelEpiComp q (kernel.ι p) ≪≫
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι p))
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _))
  have hcompact (a : A) (ι : Type (max u₁ v₁ w v)) :
      PreservesColimitsOfShape (Discrete ι)
        (preadditiveCoyoneda.obj (op (extensionByZeroUnit.{u₁, v₁, w, v} R (V a)))) := by
    let := sheafOfModules_sections_preserves_coproducts
      S.topology R (V a) (hqc _ (hV a)) ι
    exact preservesColimitsOfShape_of_natIso
      (extensionUnitCoyonedaIso.{u₁, v₁, w, v} R (V a)).symm
  obtain ⟨I, hcat, hfiltered, D, c, hpt, ⟨hc⟩, hD⟩ :=
    exists_filtered_finite_cokernels
      (fun a => extensionByZeroUnit.{u₁, v₁, w, v} R (V a))
      (fun b => extensionByZeroUnit.{u₁, v₁, w, v} R (U b)) g
      (finite_source_map_factors_through_finite_target _ _ hcompact g)
  let e' : c.pt ≅ F' := eqToIso hpt ≪≫ e
  refine ⟨I, hcat, hfiltered, D, c.ι ≫ (Functor.const I).map e'.hom,
    ⟨IsColimit.ofIsoColimit hc (Cocone.ext e' (fun i => by simp))⟩, ?_⟩
  intro i
  obtain ⟨s, t, f, ⟨ef⟩⟩ := hD i
  exact finitePresentation_of_cokernel_iso.{u₁, v₁, w, v} S R
    (fun b : t => U b.1.as) (fun a : s => V a.1.as)
    (fun b => hU _) (fun a => hV _) f (D.obj i) ef.symm

end Stacks.Sites

end
