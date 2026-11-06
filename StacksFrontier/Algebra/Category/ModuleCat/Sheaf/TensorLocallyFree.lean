module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local properties of tensor products of sheaves of modules on a ringed site

Stacks 03L6 asserts that the tensor product of two sheaves of modules on a ringed site
inherits each of the local finiteness properties of Stacks 03DL from its two factors. This
file proves the two free parts: if `F` and `G` are locally free, so is `F ⊗ G`, and if they
are finite locally free, so is `F ⊗ G`.

The argument is local and then combinatorial. Choose coverings of an object `U` trivializing
`F` and `G`; intersecting them gives a covering on whose members both factors are free, say
on bases `B_F` and `B_G`. On such a member the tensor product is the sheafification of the
tensor product of two free presheaves of modules, and the tensor product of a free module on
`B_F` with a free module on `B_G` is free on `B_F × B_G`; sheafification carries this over
because the sheafification unit is locally bijective and extension along a locally bijective
map into a sheaf is unique.

The two parts differ only in what is asked of the local bases, and `B_F × B_G` is finite as
soon as `B_F` and `B_G` are, so the argument is run once, for an arbitrary condition on the
bases closed under binary products: that is `IsLocallyFreeOnSiteWith` and
`isLocallyFreeOnSiteWith_tensor`, of which the two parts are the instances at `fun _ ↦ True`
and at `Finite`.

## Main results

* `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isLocallyFreeOnSite`: the tensor
  product of two locally free sheaves of modules on a ringed site is locally free. This is
  Stacks 03L6 part (1).
* `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite`: the
  tensor product of two finite locally free sheaves of modules on a ringed site is finite
  locally free. This is Stacks 03L6 part (2).
* `Stacks.SheafOfModules.TensorLocalProperties.isLocallyFreeOnSiteWith_tensor`: the common
  argument, for an arbitrary condition on the local bases closed under binary products.
* `Stacks.SheafOfModules.TensorLocalProperties.freeModel_over_isFree`: the sheafification of
  a coproduct of copies of the unit presheaf of modules is free on every slice.
* `Stacks.SheafOfModules.TensorLocalProperties.freeModel_tensorIso`: the tensor product of
  two such free sheaves is the free sheaf on the product of the two bases.

## Implementation notes

The free model used here is `freeModel R B`, the sheafification of the coproduct of `B`
copies of the unit presheaf of modules, rather than `SheafOfModules.free B`: it is the shape
in which the tensor product of Stacks 0GMW is computed, since that tensor product is itself a
sheafification, and `sheafificationTensorIso` compares the two sheafifications directly.
`freeModel_over_isFree` then says that this model satisfies the freeness condition of Stacks
03DL(1) on every slice, which is what the conclusion asks for.

Two extension principles along locally bijective maps are proved here rather than taken from
Mathlib. Mathlib's `PresheafOfModules.homEquivOfIsLocallyBijective` is the same bijection but
assumes `J.WEqualsLocallyBijective AddCommGrpCat`, and that assumption is not available on
the slice topologies `J.over U` where the argument needs it — it does not follow from the
corresponding assumption on `J`. So `existsUnique_moduleHom_of_locallyBijective` derives the
bijection from the type-valued statement `Presheaf.existsUnique_hom_of_isLocallyBijective`
instead, which needs no such instance, and `moduleHomEquiv_of_locallyBijective` packages it.
Because the extension is obtained from the type-valued statement, additivity and linearity of
the extension have to be checked by hand; they are checked on a covering family on which the
section in question lifts, with the restriction maps read as the semilinear maps
`PresheafOfModules.restrictₛₗ`, which is what puts the two sides of each equation in the same
module of sections.

In `tensor_over_congr`, restriction of the presheaf tensor product to a slice is compared with
the tensor product of the restrictions through the monoidal structure of
`PresheafOfModules.pushforward₀OfCommRingCat`, whose multiplication constraint is built
objectwise from identities. Comparing the two directly instead, by definitional unfolding of
the nested functors, is possible but costs about twenty times the default heartbeat budget;
going through the monoidal structure makes the comparison immediate.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe u v w

namespace Stacks.SheafOfModules.TensorLocalProperties

/-- Extension along a locally bijective morphism of presheaves of modules into a sheaf of
modules: a morphism out of the source extends uniquely to the target. -/
theorem existsUnique_moduleHom_of_locallyBijective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Cᵒᵖ ⥤ RingCat.{w}} {P Q N : PresheafOfModules.{w} R}
    (f : P ⟶ Q) [PresheafOfModules.IsLocallyInjective J f]
    [PresheafOfModules.IsLocallySurjective J f]
    (hN : Presheaf.IsSheaf J N.presheaf) (g : P ⟶ N) :
    ∃! h : Q ⟶ N, f ≫ h = g := by
  let T := PresheafOfModules.toPresheaf R ⋙
    (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat (Type w)).obj (forget _)
  have hNs : Presheaf.IsSheaf J (T.obj N) :=
    ((sheafCompose J (forget AddCommGrpCat.{w})).obj ⟨N.presheaf, hN⟩).property
  have : Presheaf.IsLocallyInjective J (T.map f) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J
      (Functor.whiskerRight ((PresheafOfModules.toPresheaf R).map f) (forget AddCommGrpCat)))
  have : Presheaf.IsLocallySurjective J (T.map f) :=
    inferInstanceAs (Presheaf.IsLocallySurjective J
      (Functor.whiskerRight ((PresheafOfModules.toPresheaf R).map f) (forget AddCommGrpCat)))
  obtain ⟨h, hh, hu⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective J
    (T.map f) (T.map g) hNs
  let φ (X : Cᵒᵖ) : Q.obj X → N.obj X := h.app X
  have hf (X : Cᵒᵖ) (x : P.obj X) : φ X (f.app X x) = g.app X x :=
    ConcreteCategory.congr_hom (congr_app hh X) x
  have hn {X Y : Cᵒᵖ} (k : X ⟶ Y) (x : Q.obj X) :
      φ Y (Q.restrictₛₗ k x) = N.restrictₛₗ k (φ X x) :=
    ConcreteCategory.congr_hom (h.naturality k) x
  let h' : Q ⟶ N := {
    app X := ModuleCat.ofHom {
      toFun := φ X
      map_add' := by
        intro x y
        apply hN.isSeparated _ _ (J.intersection_covering
          (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf R).map f) x)
          (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf R).map f) y))
        rintro Y k ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        change P.obj (Opposite.op Y) at a b
        change f.app _ a = Q.restrictₛₗ k.op x at ha
        change f.app _ b = Q.restrictₛₗ k.op y at hb
        change N.restrictₛₗ k.op (φ X (x + y)) = N.restrictₛₗ k.op (φ X x + φ X y)
        calc N.restrictₛₗ k.op (φ X (x + y))
            = φ (Opposite.op Y) (Q.restrictₛₗ k.op (x + y)) := (hn k.op (x + y)).symm
          _ = φ (Opposite.op Y) (f.app (Opposite.op Y) (a + b)) := by
              rw [map_add, map_add, ha, hb]
          _ = g.app (Opposite.op Y) (a + b) := hf _ (a + b)
          _ = g.app (Opposite.op Y) a + g.app (Opposite.op Y) b := map_add _ a b
          _ = φ (Opposite.op Y) (f.app (Opposite.op Y) a) +
                φ (Opposite.op Y) (f.app (Opposite.op Y) b) := by rw [hf, hf]
          _ = φ (Opposite.op Y) (Q.restrictₛₗ k.op x) +
                φ (Opposite.op Y) (Q.restrictₛₗ k.op y) := by rw [ha, hb]
          _ = N.restrictₛₗ k.op (φ X x) + N.restrictₛₗ k.op (φ X y) := by rw [hn, hn]
          _ = N.restrictₛₗ k.op (φ X x + φ X y) := (map_add _ _ _).symm
      map_smul' := by
        intro r x
        apply hN.isSeparated _ _
          (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf R).map f) x)
        rintro Y k ⟨a, ha⟩
        change P.obj (Opposite.op Y) at a
        change f.app _ a = Q.restrictₛₗ k.op x at ha
        change N.restrictₛₗ k.op (φ X (r • x)) = N.restrictₛₗ k.op (r • φ X x)
        calc N.restrictₛₗ k.op (φ X (r • x))
            = φ (Opposite.op Y) (Q.restrictₛₗ k.op (r • x)) := (hn k.op (r • x)).symm
          _ = φ (Opposite.op Y) (R.map k.op r • Q.restrictₛₗ k.op x) := by
              rw [map_smulₛₗ]
          _ = φ (Opposite.op Y) (R.map k.op r • f.app (Opposite.op Y) a) := by rw [ha]
          _ = φ (Opposite.op Y) (f.app (Opposite.op Y) (R.map k.op r • a)) := by
              rw [map_smul]
          _ = g.app (Opposite.op Y) (R.map k.op r • a) := hf _ _
          _ = R.map k.op r • g.app (Opposite.op Y) a := map_smul _ _ _
          _ = R.map k.op r • φ (Opposite.op Y) (f.app (Opposite.op Y) a) := by rw [hf]
          _ = R.map k.op r • φ (Opposite.op Y) (Q.restrictₛₗ k.op x) := by rw [ha]
          _ = R.map k.op r • N.restrictₛₗ k.op (φ X x) := by rw [hn]
          _ = N.restrictₛₗ k.op (r • φ X x) := (map_smulₛₗ _ _ _).symm
    }
    naturality := by
      intro X Y k
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact hn k }
  have hh' : f ≫ h' = g := by
    ext X x
    exact hf X x
  refine ⟨h', hh', ?_⟩
  intro h'' hh''
  have eq : T.map h'' = h := hu _ (by
    change T.map f ≫ T.map h'' = T.map g; rw [← T.map_comp, hh''])
  ext X x
  exact ConcreteCategory.congr_hom (congr_app eq X) x

/-- The bijection `(Q ⟶ N) ≃ (P ⟶ N)` induced by a locally bijective morphism `f : P ⟶ Q` of
presheaves of modules, when `N` is a sheaf. -/
noncomputable def moduleHomEquiv_of_locallyBijective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Cᵒᵖ ⥤ RingCat.{w}} {P Q N : PresheafOfModules.{w} R}
    (f : P ⟶ Q) [PresheafOfModules.IsLocallyInjective J f]
    [PresheafOfModules.IsLocallySurjective J f]
    (hN : Presheaf.IsSheaf J N.presheaf) : (Q ⟶ N) ≃ (P ⟶ N) :=
  Equiv.ofBijective (fun g => f ≫ g) (by
    constructor
    · intro a b h
      exact (existsUnique_moduleHom_of_locallyBijective f hN (f ≫ b)).unique h rfl
    · intro g
      exact (existsUnique_moduleHom_of_locallyBijective f hN g).exists)

/-- A family of sections exhibiting a presheaf of modules as a coproduct of copies of the unit
exhibits a sheaf of modules receiving a locally bijective map from it as the same coproduct. -/
noncomputable def isColimit_of_locallyBijective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {B : Type w}
    {P : PresheafOfModules.{w} R.obj} {M : SheafOfModules.{w} R}
    (ι : B → (PresheafOfModules.unit R.obj ⟶ P))
    (hc : IsColimit (Cofan.mk P ι)) (f : P ⟶ M.val)
    [hinj : PresheafOfModules.IsLocallyInjective J f]
    [hsurj : PresheafOfModules.IsLocallySurjective J f] :
    IsColimit (Cofan.mk M (fun b => (⟨ι b ≫ f⟩ : SheafOfModules.unit R ⟶ M))) := by
  let e (N : SheafOfModules.{w} R) := moduleHomEquiv_of_locallyBijective f N.isSheaf
  refine Cofan.IsColimit.mk _
    (fun t => ⟨(e t.pt).symm (hc.desc (Cofan.mk t.pt.val (fun b => (t.inj b).val)))⟩)
    ?_ ?_
  · intro t b
    apply SheafOfModules.hom_ext
    change (ι b ≫ f) ≫ _ = _
    rw [Category.assoc, show f ≫ _ = _ from (e t.pt).apply_symm_apply _]
    exact hc.fac _ ⟨b⟩
  · intro t m hm
    apply SheafOfModules.hom_ext
    apply (e t.pt).injective
    change f ≫ m.val = _
    rw [Equiv.apply_symm_apply]
    apply hc.hom_ext
    intro b
    rw [hc.fac]
    have h2 : (ι b.as ≫ f) ≫ m.val = (t.inj b.as).val :=
      congrArg SheafOfModules.Hom.val (hm b.as)
    change ι b.as ≫ f ≫ m.val = (t.inj b.as).val
    rw [← Category.assoc]
    exact h2

/-- Restriction of presheaves of modules to a slice site. -/
noncomputable abbrev presheafRestriction
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :=
  PresheafOfModules.pushforward.{w} (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ R))

/-- Restriction to a slice site preserves the property of being a coproduct of copies of the
unit presheaf of modules, since it is computed objectwise. -/
noncomputable def restriction_isColimit
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} (U : C)
    {B : Type w} {P : PresheafOfModules.{w} R}
    (ι : B → (PresheafOfModules.unit R ⟶ P))
    (hc : IsColimit (Cofan.mk P ι)) :
    IsColimit (Cofan.mk ((presheafRestriction R U).obj P)
      (fun b => (presheafRestriction R U).map (ι b))) := by
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro V
  exact isColimitOfPreserves (PresheafOfModules.evaluation R
    ((Over.forget U).op.obj V)) hc

/-- The sheafification unit of a presheaf of modules, as a morphism of presheaves of modules
over the same presheaf of rings. -/
noncomputable def sheafificationUnit
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {R : Sheaf J RingCat.{w}} (P : PresheafOfModules.{w} R.obj) :
    P ⟶ ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P).val where
  app U := ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P).app U
  naturality {U V} f := by
    ext x
    exact PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) f x

/-- The free sheaf of modules on `B`, in the shape in which the tensor product of Stacks 0GMW
is computed: the sheafification of the coproduct of `B` copies of the unit presheaf. -/
noncomputable abbrev freeModel
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (R : Sheaf J RingCat.{w}) (B : Type w) :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    (∐ fun _ : B => PresheafOfModules.unit R.obj)

/-- On every slice, `freeModel R B` is a coproduct of `B` copies of the restricted structure
sheaf, that is, free on `B`. -/
theorem freeModel_over_isFree
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (R : Sheaf J RingCat.{w}) (B : Type w) (U : C) :
    ∃ ι : B → (SheafOfModules.unit (R.over U) ⟶ (freeModel R B).over U),
      Nonempty (IsColimit (Cofan.mk ((freeModel R B).over U) ι)) := by
  let P := ∐ fun _ : B => PresheafOfModules.unit R.obj
  let L := presheafRestriction R.obj U
  let η := sheafificationUnit (R := R) P
  have : PresheafOfModules.IsLocallyInjective J η :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P.presheaf))
  have : PresheafOfModules.IsLocallySurjective J η :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.presheaf))
  have hi : PresheafOfModules.IsLocallyInjective (J.over U) (L.map η) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U)
      ((PresheafOfModules.toPresheaf R.obj).map η)
  have hs : PresheafOfModules.IsLocallySurjective (J.over U) (L.map η) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U)
      ((PresheafOfModules.toPresheaf R.obj).map η)
  exact ⟨_, ⟨isColimit_of_locallyBijective (hinj := hi) (hsurj := hs)
    (R := R.over U) (M := (freeModel R B).over U)
    (fun b => L.map (Sigma.ι (fun _ : B => PresheafOfModules.unit R.obj) b))
    (restriction_isColimit U _ (coproductIsCoproduct _)) (L.map η)⟩⟩

/-- Two sheaves of modules receiving locally bijective maps from isomorphic presheaves of
modules are isomorphic. -/
noncomputable def iso_of_locallyBijective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {P Q : PresheafOfModules.{w} R.obj}
    {M N : SheafOfModules.{w} R} (f : P ⟶ M.val) (g : Q ⟶ N.val)
    [hfi : PresheafOfModules.IsLocallyInjective J f]
    [hfs : PresheafOfModules.IsLocallySurjective J f]
    [hgi : PresheafOfModules.IsLocallyInjective J g]
    [hgs : PresheafOfModules.IsLocallySurjective J g] (e : P ≅ Q) : M ≅ N := by
  let ef (T : SheafOfModules.{w} R) := moduleHomEquiv_of_locallyBijective f T.isSheaf
  let eg (T : SheafOfModules.{w} R) := moduleHomEquiv_of_locallyBijective g T.isSheaf
  let a := (ef N).symm (e.hom ≫ g)
  let b := (eg M).symm (e.inv ≫ f)
  have ha : f ≫ a = e.hom ≫ g := (ef N).apply_symm_apply _
  have hb : g ≫ b = e.inv ≫ f := (eg M).apply_symm_apply _
  refine ⟨⟨a⟩, ⟨b⟩, ?_, ?_⟩
  · apply SheafOfModules.hom_ext
    apply (ef M).injective
    change f ≫ (a ≫ b) = f ≫ 𝟙 _
    rw [← Category.assoc, ha, Category.assoc, hb]
    simp
  · apply SheafOfModules.hom_ext
    apply (eg N).injective
    change g ≫ (b ≫ a) = g ≫ 𝟙 _
    rw [← Category.assoc, hb, Category.assoc, ha]
    simp

/-- The `K`-indexed family of copies of `I` exhibits `K × I` as a `K`-indexed coproduct of
copies of `I` in types. -/
def typeProdCocone (I K : Type w) :
    Cocone (Discrete.functor (fun _ : K => I)) :=
  Cocone.mk (K × I) (Discrete.natTrans fun j => ↾fun i => (j.as, i))

/-- `typeProdCocone` is a colimit. -/
def typeProdCocone_isColimit (I K : Type w) :
    IsColimit (typeProdCocone I K) := by
  refine { desc := fun s => ↾fun p => s.ι.app ⟨p.1⟩ p.2, fac := ?_, uniq := ?_ }
  · intro s j
    ext i
    rfl
  · intro s m hm
    ext p
    exact ConcreteCategory.congr_hom (hm ⟨p.1⟩) p.2

/-- In a monoidal category with coproducts, the tensor product of a coproduct of `I` copies of
the unit with a coproduct of `K` copies of the unit is a coproduct of `I × K` copies of the
unit. -/
noncomputable def tensor_coproduct_units
    {D : Type*} [Category D] [MonoidalCategory D] [HasCoproducts.{w} D]
    (I K : Type w)
    [hT : PreservesColimitsOfShape (Discrete K)
      (MonoidalCategory.tensorLeft (∐ fun _ : I => 𝟙_ D))] :
    (∐ fun _ : I => 𝟙_ D) ⊗ (∐ fun _ : K => 𝟙_ D) ≅
      (∐ fun _ : I × K => 𝟙_ D) := by
  let T := MonoidalCategory.tensorLeft (∐ fun _ : I => 𝟙_ D)
  let F := sigmaConst.obj (𝟙_ D)
  have hT := isColimitOfPreserves T (coproductIsCoproduct (fun _ : K => 𝟙_ D))
  have hF := isColimitOfPreserves F (typeProdCocone_isColimit I K)
  let η : Discrete.functor (fun _ : K => 𝟙_ D) ⋙ T ≅
      Discrete.functor (fun _ : K => I) ⋙ F :=
    Discrete.natIso (fun _ => MonoidalCategory.rightUnitor (∐ fun _ : I => 𝟙_ D))
  exact hT.coconePointsIsoOfNatIso hF η ≪≫ F.mapIso (Equiv.prodComm K I).toIso

/-- The tensor product of the free sheaves on `I` and on `K` is the free sheaf on `I × K`. -/
noncomputable def freeModel_tensorIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (O : Sheaf J CommRingCat.{w}) (I K : Type w) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj (freeModel
        (Stacks.SheafOfModules.Tensor.ringSheaf O) I)).obj (freeModel
        (Stacks.SheafOfModules.Tensor.ringSheaf O) K) ≅
      freeModel (Stacks.SheafOfModules.Tensor.ringSheaf O) (I × K) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O
  let P := ∐ fun _ : I => PresheafOfModules.unit R.obj
  let Q := ∐ fun _ : K => PresheafOfModules.unit R.obj
  haveI : Presheaf.IsLocallyInjective J
      (AlgebraicGeometry.SheafOfModules.associatedRingMap J (𝟙 O.obj)) := by
    change Presheaf.IsLocallyInjective J (𝟙 (O.obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  haveI : Presheaf.IsLocallySurjective J
      (AlgebraicGeometry.SheafOfModules.associatedRingMap J (𝟙 O.obj)) := by
    change Presheaf.IsLocallySurjective J (𝟙 (O.obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  have hT0 : PreservesColimitsOfSize.{w, w}
      (tensorLeft (show PresheafOfModules.{w}
        (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) from P)) := inferInstance
  have hT : PreservesColimitsOfShape (Discrete K) (tensorLeft P) :=
    hT0.preservesColimitsOfShape
  haveI : HasCoproducts.{w} (PresheafOfModules.{w} R.obj) := fun _ =>
    PresheafOfModules.hasColimitsOfShape _ _
  exact (_root_.PresheafOfModules.sheafificationTensorIso J (𝟙 O.obj)).app (P, Q) ≪≫
    (PresheafOfModules.sheafification (𝟙 R.obj)).mapIso (tensor_coproduct_units (hT := hT) I K)

/-- The tensor product of two sheaves of modules, restricted to a slice, only depends on the
restrictions of the two factors. -/
noncomputable def tensor_over_congr
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (O : Sheaf J CommRingCat.{w}) (U : C)
    {F G F' G' : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (eF : F.over U ≅ F'.over U) (eG : G.over U ≅ G'.over U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G).over U ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F').obj G').over U := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O
  let L := presheafRestriction R.obj U
  let P := F.val ⊗ G.val
  let Q := F'.val ⊗ G'.val
  let f := L.map (sheafificationUnit (R := R) P)
  let g := L.map (sheafificationUnit (R := R) Q)
  have inj (A : PresheafOfModules.{w} R.obj) :
      PresheafOfModules.IsLocallyInjective (J.over U)
        (L.map (sheafificationUnit (R := R) A)) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U)
      (CategoryTheory.toSheafify J A.presheaf)
  have surj (A : PresheafOfModules.{w} R.obj) :
      PresheafOfModules.IsLocallySurjective (J.over U)
        (L.map (sheafificationUnit (R := R) A)) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U)
      (CategoryTheory.toSheafify J A.presheaf)
  letI := inj P
  letI := inj Q
  letI := surj P
  letI := surj Q
  let pf := PresheafOfModules.pushforward₀OfCommRingCat.{w} (Over.forget U) O.obj
  letI : MonoidalCategory (PresheafOfModules.{w} ((Over.forget U).op ⋙ R.obj)) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := (Over.forget U).op ⋙ O.obj)
  let eFv : pf.obj F.val ≅ pf.obj F'.val :=
    (SheafOfModules.forget (R.over U)).mapIso eF
  let eGv : pf.obj G.val ≅ pf.obj G'.val :=
    (SheafOfModules.forget (R.over U)).mapIso eG
  let e : L.obj P ≅ L.obj Q :=
    (Functor.Monoidal.μIso pf F.val G.val).symm ≪≫ (eFv ⊗ᵢ eGv) ≪≫
      Functor.Monoidal.μIso pf F'.val G'.val
  exact iso_of_locallyBijective (hfi := inj P) (hfs := surj P)
    (hgi := inj Q) (hgs := surj Q) (R := R.over U)
    (M := (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G).over U)
    (N := (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F').obj G').over U) f g e

/-- An isomorphism of the restrictions of two sheaves of modules to `V` restricts further along
any morphism `g : W ⟶ V`. -/
private noncomputable def restrictOverIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) {V W : C} (g : W ⟶ V) {A B : SheafOfModules.{w} R}
    (e : A.over V ≅ B.over V) : A.over W ≅ B.over W :=
  ((SheafOfModules.overFunctorMap R g).app A).symm ≪≫
    (SheafOfModules.overMap R g).mapIso e ≪≫ (SheafOfModules.overFunctorMap R g).app B

/-- **Local freeness with a constraint on the local bases.** Every object has a covering family
on whose members the module is a coproduct of copies of the restricted structure sheaf, indexed
by a type satisfying `P`.

Taking `P` to be `fun _ ↦ True` gives `SheafOfModules.IsLocallyFreeOnSite`, Stacks 03DL(1), and
taking it to be `Finite` gives `SheafOfModules.IsFiniteLocallyFreeOnSite`, Stacks 03DL(2); the
two comparisons are `isLocallyFreeOnSiteWith_true_iff` and `isLocallyFreeOnSiteWith_finite_iff`.
A tensor product multiplies the two local bases, so it inherits the condition for every `P`
closed under binary products, and parts (1) and (2) of Stacks 03L6 are the two instances of the
single argument `isLocallyFreeOnSiteWith_tensor`. -/
@[ega "0 5.4.1"]
def IsLocallyFreeOnSiteWith {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (P : Type w → Prop) (F : SheafOfModules.{w} R) : Prop :=
  ∀ U : C,
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      (Sieve.ofArrows V f ∈ J U) ∧
        ∀ i : I, ∃ B : Type w, P B ∧
          ∃ ι : ∀ _ : B, SheafOfModules.unit (R.over (V i)) ⟶ F.over (V i),
            Nonempty (IsColimit (Cofan.mk (F.over (V i)) ι))

/-- With no constraint on the local bases, `IsLocallyFreeOnSiteWith` is local freeness in the
sense of Stacks 03DL(1). -/
theorem isLocallyFreeOnSiteWith_true_iff {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w}) (F : SheafOfModules.{w} R) :
    IsLocallyFreeOnSiteWith R (fun _ ↦ True) F ↔ SheafOfModules.IsLocallyFreeOnSite F := by
  simp only [IsLocallyFreeOnSiteWith, SheafOfModules.IsLocallyFreeOnSite, true_and]

/-- With the local bases constrained to be finite, `IsLocallyFreeOnSiteWith` is finite local
freeness in the sense of Stacks 03DL(2).

The condition of Stacks 03DL(2) names the rank, so the two index types are compared by the
reindexing of a colimiting cofan along an equivalence: `Finite.equivFin` in one direction and
`Equiv.ulift` in the other, the latter because a rank is a `Fin n` and a local basis of
`IsLocallyFreeOnSiteWith` is indexed in the module universe. -/
theorem isLocallyFreeOnSiteWith_finite_iff {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w}) (F : SheafOfModules.{w} R) :
    IsLocallyFreeOnSiteWith R Finite F ↔ SheafOfModules.IsFiniteLocallyFreeOnSite F := by
  rw [SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit]
  refine forall_congr' fun U => ?_
  constructor
  · rintro ⟨I, V, f, hcov, hfree⟩
    refine ⟨I, V, f, hcov, fun i => ?_⟩
    obtain ⟨B, hB, ι, ⟨hι⟩⟩ := hfree i
    have := hB
    exact ⟨Nat.card B, fun j => ι ((Finite.equivFin B).symm j),
      ⟨Cofan.isColimitEquivOfEquiv (Finite.equivFin B).symm (Cofan.mk (F.over (V i)) ι) hι⟩⟩
  · rintro ⟨I, V, f, hcov, hfree⟩
    refine ⟨I, V, f, hcov, fun i => ?_⟩
    obtain ⟨n, ι, ⟨hι⟩⟩ := hfree i
    exact ⟨ULift.{w} (Fin n), inferInstance, fun b => ι b.down,
      ⟨Cofan.isColimitEquivOfEquiv Equiv.ulift (Cofan.mk (F.over (V i)) ι) hι⟩⟩

/-- **The tensor product multiplies local bases.** If `F` and `G` are locally free with their
local bases constrained by a predicate `P` closed under binary products, then so is `F ⊗ G`.

Intersecting a covering trivializing `F` with one trivializing `G` gives a covering on whose
members both factors are free, on bases `B_F` and `B_G` carried along by the two arrows into
the respective members; `freeModel_tensorIso` makes the tensor product free on `B_F × B_G`
there, and `tensor_over_congr` transports it along the two trivializations. -/
theorem isLocallyFreeOnSiteWith_tensor (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {P : Type w → Prop} (hP : ∀ {A B : Type w}, P A → P B → P (A × B))
    {F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hF : IsLocallyFreeOnSiteWith (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P F)
    (hG : IsLocallyFreeOnSiteWith (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P G) :
    IsLocallyFreeOnSiteWith (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G) := by
  intro U
  obtain ⟨IF, VF, fF, hFcov, hFfree⟩ := hF U
  obtain ⟨IG, VG, fG, hGcov, hGfree⟩ := hG U
  let SF : Sieve U := Sieve.ofArrows VF fF
  let SG : Sieve U := Sieve.ofArrows VG fG
  let K : Type (max u v) := {p : Σ V : X.C, V ⟶ U // SF p.2 ∧ SG p.2}
  let W : K → X.C := fun p => p.1.1
  let fW : ∀ p, W p ⟶ U := fun p => p.1.2
  have hle : SF ⊓ SG ≤ Sieve.ofArrows W fW := by
    intro V g hg
    exact Sieve.ofArrows_mk W fW ⟨⟨V, g⟩, hg⟩
  have hWcov : Sieve.ofArrows W fW ∈ X.J U :=
    X.J.superset_covering hle (X.J.intersection_covering hFcov hGcov)
  refine ⟨K, W, fW, hWcov, ?_⟩
  intro p
  obtain ⟨iF, gF, hgF⟩ := (Sieve.mem_ofArrows_iff VF fF (fW p)).1 p.2.1
  obtain ⟨iG, gG, hgG⟩ := (Sieve.mem_ofArrows_iff VG fG (fW p)).1 p.2.2
  obtain ⟨BF, hBF, ιF, hιF⟩ := hFfree iF
  obtain ⟨BG, hBG, ιG, hιG⟩ := hGfree iG
  obtain ⟨hιF⟩ := hιF
  obtain ⟨hιG⟩ := hιG
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  obtain ⟨κF, hκF⟩ := freeModel_over_isFree R BF (VF iF)
  obtain ⟨κG, hκG⟩ := freeModel_over_isFree R BG (VG iG)
  let eF : F.over (VF iF) ≅ (freeModel R BF).over (VF iF) :=
    hιF.coconePointUniqueUpToIso hκF.some
  let eG : G.over (VG iG) ≅ (freeModel R BG).over (VG iG) :=
    hιG.coconePointUniqueUpToIso hκG.some
  let eF' : F.over (W p) ≅ (freeModel R BF).over (W p) := restrictOverIso R gF eF
  let eG' : G.over (W p) ≅ (freeModel R BG).over (W p) := restrictOverIso R gG eG
  let e := tensor_over_congr X.O (W p) eF' eG' ≪≫
    (SheafOfModules.overFunctor R (W p)).mapIso (freeModel_tensorIso X.O BF BG)
  obtain ⟨κ, hκ⟩ := freeModel_over_isFree R (BF × BG) (W p)
  refine ⟨BF × BG, hP hBF hBG, (fun b => κ b ≫ e.inv), ⟨?_⟩⟩
  exact hκ.some.ofIsoColimit (Cofan.ext e.symm (fun b => rfl))

/-- **Stacks Project, Tag 03L6, part (1).** The tensor product of two locally free sheaves of
modules on a ringed site is locally free. -/
@[stacks 03L6 "locally_free"]
theorem tensorSheaf_isLocallyFreeOnSite (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : SheafOfModules.IsLocallyFreeOnSite F)
    (hG : SheafOfModules.IsLocallyFreeOnSite G) :
    SheafOfModules.IsLocallyFreeOnSite
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        (F, G)) :=
  (isLocallyFreeOnSiteWith_true_iff (Stacks.SheafOfModules.Tensor.ringSheaf X.O) _).1
    (isLocallyFreeOnSiteWith_tensor X (P := fun _ ↦ True) (fun _ _ => trivial)
      ((isLocallyFreeOnSiteWith_true_iff (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F).2 hF)
      ((isLocallyFreeOnSiteWith_true_iff (Stacks.SheafOfModules.Tensor.ringSheaf X.O) G).2 hG))

/-- **Stacks Project, Tag 03L6, part (2).** The tensor product of two finite locally free
sheaves of modules on a ringed site is finite locally free. -/
@[stacks 03L6 "finite_locally_free"]
theorem tensorSheaf_isFiniteLocallyFreeOnSite (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : SheafOfModules.IsFiniteLocallyFreeOnSite F)
    (hG : SheafOfModules.IsFiniteLocallyFreeOnSite G) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        (F, G)) :=
  (isLocallyFreeOnSiteWith_finite_iff (Stacks.SheafOfModules.Tensor.ringSheaf X.O) _).1
    (isLocallyFreeOnSiteWith_tensor X (P := Finite)
      (fun hA hB => @Finite.instProd _ _ hA hB)
      ((isLocallyFreeOnSiteWith_finite_iff (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F).2 hF)
      ((isLocallyFreeOnSiteWith_finite_iff (Stacks.SheafOfModules.Tensor.ringSheaf X.O) G).2 hG))

end Stacks.SheafOfModules.TensorLocalProperties

end
