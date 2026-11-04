module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentChaoticSite
public import StacksFrontier.Homology.ExtendScalars.Flat
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# Quasi-coherent modules on a chaotic flat site

If the topology is chaotic and all restriction homomorphisms of the structure
sheaf are flat, quasi-coherent modules form a weak Serre subcategory of the
category of sheaves of modules.

## Main results

* `Stacks.Sheaves.ChaoticFlatQuasicoherent.isQuasicoherentOnSite_isWeakSerreClass`: on a chaotic
  ringed site with flat restriction homomorphisms, quasi-coherent modules form a weak Serre
  subcategory of the sheaves of modules.

## Implementation notes

The chaotic topology is expressed by `Fact (X.J = ⊥)`. Flatness is imposed on every
restriction homomorphism, and quasi-coherence is the general predicate on
sheaves of modules over a ringed site. The weak Serre property is expressed by
`ObjectProperty.IsWeakSerreClass`.

## References

* [Stacks Project, Tag 0GZP](https://stacks.math.columbia.edu/tag/0GZP)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace Stacks.Sheaves.ChaoticFlatQuasicoherent

universe u v r m u₁ v₁ u₂ v₂
universe t r' m'

private theorem chaoticSheafify (X : RingedSite.{u, v, r}) (hX : X.J = ⊥) :
    HasSheafify X.J AddCommGrpCat.{m} := by
  rw [hX]
  infer_instance

private theorem chaoticWEqualsLocallyBijective
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥) :
    X.J.WEqualsLocallyBijective AddCommGrpCat.{m} := by
  let : HasSheafify X.J AddCommGrpCat.{m} := chaoticSheafify X hX
  let : ∀ P : X.Cᵒᵖ ⥤ AddCommGrpCat.{m}, IsIso (toSheafify X.J P) := fun P =>
    isIso_toSheafify _ (by rw [hX]; exact Presheaf.isSheaf_bot P)
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' X.J AddCommGrpCat

/-- On a chaotic site the sheafification of abelian-group-valued presheaves exists. -/
local instance chaoticHasSheafify (X : RingedSite.{u, v, r}) [Fact (X.J = ⊥)] :
    HasSheafify X.J AddCommGrpCat.{m} :=
  chaoticSheafify X Fact.out

/-- On a chaotic site sheafification inverts exactly the locally bijective morphisms. -/
local instance chaoticWEqualsLocallyBijective' (X : RingedSite.{u, v, r}) [Fact (X.J = ⊥)] :
    X.J.WEqualsLocallyBijective AddCommGrpCat.{m} :=
  chaoticWEqualsLocallyBijective X Fact.out

private theorem chaoticSheafToPresheaf_isEquivalence
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (hJ : J = ⊥) :
    (sheafToPresheaf J AddCommGrpCat.{m}).IsEquivalence := by
  subst J
  exact Equivalence.isEquivalence_functor (sheafBotEquivalence AddCommGrpCat.{m})

private instance evaluation_additive
    (X : RingedSite.{u, v, r}) (U : X.C) :
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
  ⟨fun {_ _} _ _ => rfl⟩

private instance evaluation_preservesZeroMorphisms
    (X : RingedSite.{u, v, r}) (U : X.C) :
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (op U)).PreservesZeroMorphisms :=
  ⟨by intro F G; rfl⟩

private theorem evaluation_map_exact
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥) (U : X.C)
    (S : ShortComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hS : S.Exact) :
    (S.map (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (op U))).Exact := by
  let : HasSheafify X.J AddCommGrpCat.{m} := chaoticSheafify X hX
  let : X.J.WEqualsLocallyBijective AddCommGrpCat.{m} :=
    chaoticWEqualsLocallyBijective X hX
  let : Functor.IsEquivalence (sheafToPresheaf X.J AddCommGrpCat.{m}) :=
    chaoticSheafToPresheaf_isEquivalence hX
  rw [ShortComplex.exact_iff_exact_map_forget₂]
  exact ((hS.map (SheafOfModules.toSheaf.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map
    (sheafToPresheaf X.J AddCommGrpCat.{m})).map
      ((CategoryTheory.evaluation X.Cᵒᵖ AddCommGrpCat.{m}).obj (op U))

private theorem composableArrows_map_exact
    {A : Type u₁} [Category.{v₁} A] [Preadditive A] [HasZeroMorphisms A]
    {B : Type u₂} [Category.{v₂} B] [Preadditive B] [HasZeroMorphisms B]
    (F : A ⥤ B) [F.Additive] [F.PreservesZeroMorphisms]
    (S : ComposableArrows A 4) (hS : S.Exact)
    (hmap : ∀ T : ShortComplex A, T.Exact → (T.map F).Exact) :
    ((F.mapComposableArrows 4).obj S).Exact := by
  refine ⟨⟨fun i hi => ?_⟩, fun i hi => hmap _ (hS.exact i hi)⟩
  change F.map (S.map' i (i + 1)) ≫ F.map (S.map' (i + 1) (i + 2)) = 0
  rw [← F.map_comp, hS.toIsComplex.zero' i (i + 1) (i + 2), F.map_zero]

/-- Semilinearity of a restriction map read through a ring isomorphism of the coefficient
sheaves. -/
private theorem transport_map_smul {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {R' : Sheaf J RingCat.{r'}}
    (e : ∀ A, R'.obj.obj A ≃+* R.obj.obj A)
    (he : ∀ {A B} (f : A ⟶ B) (a : R'.obj.obj A),
      e B (R'.obj.map f a) = R.obj.map f (e A a))
    (M : SheafOfModules.{t} R) {A B : Cᵒᵖ} (f : A ⟶ B) (a : R'.obj.obj A)
    (x : M.val.obj A) :
    M.val.map f (e A a • x) = e B (R'.obj.map f a) • M.val.map f x :=
  (M.val.map_smul f (e A a) x).trans
    (congrArg (fun scalar => scalar • M.val.map f x) (he f a).symm)

private noncomputable def transportModules
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {R' : Sheaf J RingCat.{r'}}
    (e : ∀ A, R'.obj.obj A ≃+* R.obj.obj A)
    (he : ∀ {A B} (f : A ⟶ B) (a : R'.obj.obj A),
      e B (R'.obj.map f a) = R.obj.map f (e A a)) :
    SheafOfModules.{t} R ⥤ SheafOfModules.{t} R' where
  obj M := {
    val := {
      obj A := (ModuleCat.restrictScalars (e A).toRingHom).obj (M.val.obj A)
      map := fun {A B} f => ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars (e A).toRingHom).obj (M.val.obj A))
        (Y := (ModuleCat.restrictScalars (R'.obj.map f).hom).obj
          ((ModuleCat.restrictScalars (e B).toRingHom).obj (M.val.obj B))) {
        toFun := M.val.map f
        map_add' := map_add (M.val.map f).hom
        map_smul' := fun a element => transport_map_smul e he M f a element }
      map_id A := by
        ext element
        exact congrArg (fun map => map.hom element) (M.val.map_id A)
      map_comp f g := by
        ext element
        exact M.val.map_comp_apply f g element }
    isSheaf := M.isSheaf }
  map α := ⟨{
    app A := (ModuleCat.restrictScalars (e A).toRingHom).map (α.val.app A)
    naturality f := by
      ext element
      exact PresheafOfModules.naturality_apply α.val f element }⟩

/-- Transporting modules along `e` and then along `e.symm` is isomorphic to the identity. -/
private noncomputable def transportModules_unitIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {R' : Sheaf J RingCat.{r'}}
    (e : ∀ A, R'.obj.obj A ≃+* R.obj.obj A)
    (he : ∀ {A B} (f : A ⟶ B) (a : R'.obj.obj A),
      e B (R'.obj.map f a) = R.obj.map f (e A a))
    (he' : ∀ {A B} (f : A ⟶ B) (a : R.obj.obj A),
      (e B).symm (R.obj.map f a) = R'.obj.map f ((e A).symm a)) :
    𝟭 (SheafOfModules.{t} R) ≅ transportModules.{u, v, r, t, r'} (R := R) (R' := R') e he ⋙
      transportModules.{u, v, r', t, r} (R := R') (R' := R) (fun A => (e A).symm) he' := by
  let G := transportModules e he ⋙ transportModules (fun A => (e A).symm) he'
  refine NatIso.ofComponents (fun M => ?_) ?_
  · refine (SheafOfModules.fullyFaithfulForget R).preimageIso
      (PresheafOfModules.isoMk (fun A => ?_) ?_)
    · exact {
        hom := ModuleCat.ofHom (X := M.val.obj A) (Y := (G.obj M).val.obj A) {
          toFun := id
          map_add' := fun _ _ => rfl
          map_smul' := fun a element => by
            show a • element = e A ((e A).symm a) • element
            rw [RingEquiv.apply_symm_apply] }
        inv := ModuleCat.ofHom (X := (G.obj M).val.obj A) (Y := M.val.obj A) {
          toFun := id
          map_add' := fun _ _ => rfl
          map_smul' := fun a element => by
            show e A ((e A).symm a) • (show M.val.obj A from element) =
              a • (show M.val.obj A from element)
            rw [RingEquiv.apply_symm_apply] } }
    · intro A B f; ext element; rfl
  · intro M N α; ext A element; rfl

private theorem transportModules_isEquivalence
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {R' : Sheaf J RingCat.{r'}}
    (e : ∀ A, R'.obj.obj A ≃+* R.obj.obj A)
    (he : ∀ {A B} (f : A ⟶ B) (a : R'.obj.obj A),
      e B (R'.obj.map f a) = R.obj.map f (e A a)) :
    (transportModules.{u, v, r, t, r'} (R := R) (R' := R') e he).IsEquivalence := by
  have he' : ∀ {A B} (f : A ⟶ B) (a : R.obj.obj A),
      (e B).symm (R.obj.map f a) = R'.obj.map f ((e A).symm a) := by
    intro A B f a
    apply (e B).injective
    simp only [RingEquiv.apply_symm_apply, he]
  exact Functor.IsEquivalence.mk'
    (transportModules.{u, v, r', t, r} (R := R') (R' := R) (fun A => (e A).symm) he')
    (transportModules_unitIso.{u, v, r, t, r'} e he he')
    (transportModules_unitIso.{u, v, r', t, r} (fun A => (e A).symm) he' he).symm

private noncomputable def liftedSite
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥) : RingedSite.{u, v, max u v r m} where
  C := X.C
  J := X.J
  O := ⟨{
    obj A := CommRingCat.of (ULift.{max u v m} (X.O.obj.obj A))
    map f := CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp
        ((X.O.obj.map f).hom.comp ULift.ringEquiv.toRingHom))
    map_id A := by
      ext element
      exact congrArg (fun map => map.hom element.down) (X.O.obj.map_id A)
    map_comp f g := by
      ext element
      exact congrArg (fun map => map.hom element.down) (X.O.obj.map_comp f g) },
    (congrArg (fun J => Presheaf.IsSheaf J _) hX).mpr (Presheaf.isSheaf_bot _)⟩

attribute [local implicit_reducible] liftedSite

private noncomputable def liftedModule
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥)
    (M : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.{max u v r m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (liftedSite.{u, v, r, m} X hX).O) :=
  (transportModules (fun _ => ULift.ringEquiv) (by intros; rfl)).obj
    (SheafOfModules.uliftForPresentation.{u, v, r, m, max u v r} M)

private noncomputable def hasPresentation
    {A : Type u₁} [Category.{v₁} A] [HasZeroMorphisms A] (unit target : A) : Prop :=
  ∃ (I K : Type t) (P Q : A) (ι : I → (unit ⟶ P)) (κ : K → (unit ⟶ Q)),
    Nonempty (IsColimit (Cofan.mk P ι)) ∧ Nonempty (IsColimit (Cofan.mk Q κ)) ∧
      ∃ (a : Q ⟶ P) (b : P ⟶ target) (hab : a ≫ b = 0),
        Nonempty (IsColimit (CokernelCofork.ofπ b hab))

private theorem hasPresentation_map
    {A : Type u₁} [Category.{v₁} A] [HasZeroMorphisms A]
    {B : Type u₂} [Category.{v₂} B] [HasZeroMorphisms B]
    (F : A ⥤ B) [F.IsEquivalence] [F.PreservesZeroMorphisms]
    {unit target : A} {unit' target' : B}
    (unitIso : F.obj unit ≅ unit') (targetIso : F.obj target ≅ target')
    (h : hasPresentation.{u₁, v₁, t} unit target) :
    hasPresentation.{u₂, v₂, t} unit' target' := by
  classical
  obtain ⟨I, K, P, Q, ι, κ, hP, hQ, a, b, hab, hb⟩ := h
  let ι' := fun i => unitIso.inv ≫ F.map (ι i)
  let κ' := fun i => unitIso.inv ≫ F.map (κ i)
  have cofanMap : ∀ {Z : A} {L : Type t} (maps : L → (unit ⟶ Z)),
      IsColimit (Cofan.mk Z maps) →
        IsColimit (Cofan.mk (F.obj Z) (fun i => unitIso.inv ≫ F.map (maps i))) := by
    intro Z L maps hmaps
    have hc := (Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk Z maps)).toFun
      (isColimitOfPreserves F hmaps)
    refine Cofan.IsColimit.mk _ (fun cone => Cofan.IsColimit.desc hc
      (fun i => unitIso.hom ≫ cone.inj i)) ?_ ?_
    · intro cone i
      show (unitIso.inv ≫ F.map (maps i)) ≫ _ = _
      have hfac := Cofan.IsColimit.fac hc
        (fun i => unitIso.hom ≫ cone.inj i) i
      dsimp at hfac
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun morphism => unitIso.inv ≫ morphism) hfac).trans
          (unitIso.inv_hom_id_assoc _))
    · intro cone map hmap
      apply Cofan.IsColimit.hom_ext hc
      intro i
      have hi := congrArg (fun morphism => unitIso.hom ≫ morphism) (hmap i)
      have hfac := Cofan.IsColimit.fac hc
        (fun i => unitIso.hom ≫ cone.inj i) i
      dsimp at hfac
      simpa [Category.assoc, hfac] using hi
  let b' := F.map b ≫ targetIso.hom
  have hab' : F.map a ≫ b' = 0 := by
    simp [b', ← Category.assoc, ← F.map_comp, hab]
  have hb' : IsColimit (CokernelCofork.ofπ b' hab') :=
    IsColimit.ofIsoColimit (CokernelCofork.mapIsColimit _ hb.some F) (Cofork.ext targetIso rfl)
  exact ⟨I, K, F.obj P, F.obj Q, ι', κ', ⟨cofanMap ι hP.some⟩,
    ⟨cofanMap κ hQ.some⟩, F.map a, b', hab', ⟨hb'⟩⟩

private theorem hasPresentation_iff
    {A : Type u₁} [Category.{v₁} A] [HasZeroMorphisms A]
    {B : Type u₂} [Category.{v₂} B] [HasZeroMorphisms B]
    (F : A ⥤ B) [F.IsEquivalence] [F.PreservesZeroMorphisms]
    {unit target : A} {unit' target' : B}
    (unitIso : F.obj unit ≅ unit') (targetIso : F.obj target ≅ target') :
    hasPresentation.{u₁, v₁, t} unit target ↔
      hasPresentation.{u₂, v₂, t} unit' target' :=
  ⟨hasPresentation_map F unitIso targetIso, hasPresentation_map F.asEquivalence.inverse
    ((F.asEquivalence.inverse.mapIso unitIso).symm ≪≫ (F.asEquivalence.unitIso.app unit).symm)
    ((F.asEquivalence.inverse.mapIso targetIso).symm ≪≫ (F.asEquivalence.unitIso.app target).symm)⟩

private theorem liftedModule_quasicoherent_iff
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥)
    (M : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (liftedModule.{u, v, r, m} X hX M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite := by
  have presentation : ∀ U : X.C,
      (M.over U).HasGlobalPresentation ↔
        ((liftedModule.{u, v, r, m} X hX M).over U).HasGlobalPresentation := by
    intro U
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U
    let R' := (Stacks.SheafOfModules.Tensor.ringSheaf (liftedSite.{u, v, r, m} X hX).O).over U
    let e : ∀ A, R'.obj.obj A ≃+* R.obj.obj A := fun _ => ULift.ringEquiv
    have he : ∀ {A B} (f : A ⟶ B) (a : R'.obj.obj A),
        e B (R'.obj.map f a) = R.obj.map f (e A a) := by intros; rfl
    let F := transportModules.{max u v, v, r, max u v r m, max u v r m} e he
    have : F.IsEquivalence := transportModules_isEquivalence e he
    have : F.Additive := ⟨by intros; rfl⟩
    let unit := SheafOfModules.uliftForPresentation.{max u v, v, r, r, max u v m}
      (SheafOfModules.unit R)
    let unit' := SheafOfModules.uliftForPresentation.{max u v, v, max u v r m,
      max u v r m, max u v r m} (SheafOfModules.unit R')
    let target := SheafOfModules.uliftForPresentation.{max u v, v, r, m, max u v r}
      (M.over U)
    let target' := SheafOfModules.uliftForPresentation.{max u v, v, max u v r m,
      max u v r m, max u v r m} ((liftedModule.{u, v, r, m} X hX M).over U)
    have unitIso : F.obj unit ≅ unit' := by
      refine (SheafOfModules.fullyFaithfulForget R').preimageIso
        (PresheafOfModules.isoMk (fun A => ?_) ?_)
      · exact {
          hom := ModuleCat.ofHom (X := (F.obj unit).val.obj A) (Y := unit'.val.obj A) {
            toFun := fun element => ULift.up (ULift.up element.down)
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
          inv := ModuleCat.ofHom (X := unit'.val.obj A) (Y := (F.obj unit).val.obj A) {
            toFun := fun element => ULift.up element.down.down
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl } }
      · intro A B f; ext; rfl
    have targetIso : F.obj target ≅ target' := by
      refine (SheafOfModules.fullyFaithfulForget R').preimageIso
        (PresheafOfModules.isoMk (fun A => ?_) ?_)
      · exact {
          hom := ModuleCat.ofHom (X := (F.obj target).val.obj A) (Y := target'.val.obj A) {
            toFun := fun element => ULift.up (ULift.up element.down)
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
          inv := ModuleCat.ofHom (X := target'.val.obj A) (Y := (F.obj target).val.obj A) {
            toFun := fun element => ULift.up element.down.down
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl } }
      · intro A B f; ext element; rfl
    exact hasPresentation_iff F unitIso targetIso
  refine ⟨fun h => ⟨fun U => ?_⟩, fun h => ⟨fun U => ?_⟩⟩ <;>
    obtain ⟨I, V, f, hcover, hpres⟩ := h.locally_hasGlobalPresentation U
  · exact ⟨I, V, f, hcover, fun i => (presentation (V i)).mpr (hpres i)⟩
  · exact ⟨I, V, f, hcover, fun i => (presentation (V i)).mp (hpres i)⟩

private noncomputable def evaluationLifted
    (X : RingedSite.{u, v, r}) (U : X.C) :
    SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      ModuleCat.{max u v r m}
        (CommRingCat.of (ULift.{max u v m} (X.O.obj.obj (op U)))) :=
    SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U) ⋙
      ModuleCat.uliftFunctor.{max u v r, m}
        (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)) ⋙
        ModuleCat.restrictScalars ULift.ringEquiv.toRingHom

/-- The restriction map of the universe-raised module along `f`, with its source and target
named by `evaluationLifted`. -/
private noncomputable def restrictionMapLifted
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥)
    (F : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {U V : X.C} (f : U ⟶ V) :
    (evaluationLifted.{u, v, r, m} X V).obj F ⟶
      (ModuleCat.restrictScalars
        ((liftedSite.{u, v, r, m} X hX).O.obj.map f.op).hom).obj
        ((evaluationLifted.{u, v, r, m} X U).obj F) :=
  (liftedModule.{u, v, r, m} X hX F).val.map f.op

private theorem restrictionMapLifted_naturality
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥) {U V : X.C} (f : U ⟶ V)
    {F G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (α : F ⟶ G) :
    (evaluationLifted.{u, v, r, m} X V).map α ≫ restrictionMapLifted X hX G f =
      restrictionMapLifted X hX F f ≫
        (ModuleCat.restrictScalars
          ((liftedSite.{u, v, r, m} X hX).O.obj.map f.op).hom).map
          ((evaluationLifted.{u, v, r, m} X U).map α) := by
  ext element
  exact congrArg ULift.up (congrArg (fun map => map.hom element.down)
    (α.val.naturality f.op).symm)

/-- The comparison map of the universe-raised module on the universe-raised site, with its
source and target named by `evaluationLifted`. -/
private noncomputable def canonicalMapLifted
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥)
    (F : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {U V : X.C} (f : U ⟶ V) :
    (ModuleCat.extendScalars.{max u v r m, max u v r m, max u v r m}
        ((liftedSite.{u, v, r, m} X hX).O.obj.map f.op).hom).obj
        ((evaluationLifted.{u, v, r, m} X V).obj F) ⟶
      (evaluationLifted.{u, v, r, m} X U).obj F :=
  Stacks.SheafOfModules.canonicalMap (liftedSite.{u, v, r, m} X hX)
    (liftedModule.{u, v, r, m} X hX F) f

private theorem isQuasicoherent_iff_canonicalMapLifted_isIso
    (X : RingedSite.{u, v, r}) (F : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hX : X.J = ⊥) :
    F.IsQuasicoherentOnSite ↔
      ∀ ⦃U V : X.C⦄ (f : U ⟶ V), IsIso (canonicalMapLifted X hX F f) :=
  (liftedModule_quasicoherent_iff X hX F).symm.trans
    (Stacks.SheafOfModules.isQuasicoherent_iff_canonicalMap_isIso
      (liftedSite.{u, v, r, m} X hX) (liftedModule.{u, v, r, m} X hX F) hX)

private theorem liftedRestriction_flat
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥)
    {U V : X.C} (f : U ⟶ V) (hf : RingHom.Flat (X.O.obj.map f.op).hom) :
    RingHom.Flat ((liftedSite.{u, v, r, m} X hX).O.obj.map f.op).hom :=
  .comp (.comp (.of_bijective ULift.ringEquiv.bijective) hf)
    (.of_bijective ULift.ringEquiv.symm.bijective)

private instance evaluationLifted_additive
    (X : RingedSite.{u, v, r}) (U : X.C) :
    (evaluationLifted.{u, v, r, m} X U).Additive :=
  ⟨fun {_ _} _ _ => rfl⟩

private instance evaluationLifted_preservesZeroMorphisms
    (X : RingedSite.{u, v, r}) (U : X.C) :
    (evaluationLifted.{u, v, r, m} X U).PreservesZeroMorphisms :=
  ⟨by intro F G; rfl⟩

private theorem extendScalars_map_exact_lifted
    {R S : Type r} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : RingHom.Flat f) (T : ShortComplex (ModuleCat.{max r m} R))
    (hT : T.Exact) :
    (T.map (ModuleCat.extendScalars.{r, r, max r m} f)).Exact := by
  algebraize [f]
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
  show Function.Exact (LinearMap.lTensor S T.f.hom) (LinearMap.lTensor S T.g.hom)
  let : Module.Flat R S := hf
  exact Module.Flat.lTensor_exact S hT

private theorem canonicalMapLifted_naturality
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥) {U V : X.C} (f : U ⟶ V)
    {F G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (α : F ⟶ G) :
    (ModuleCat.extendScalars.{max u v r m, max u v r m, max u v r m}
      ((liftedSite.{u, v, r, m} X hX).O.obj.map f.op).hom).map
        ((evaluationLifted X V).map α) ≫ canonicalMapLifted X hX G f =
      canonicalMapLifted X hX F f ≫ (evaluationLifted X U).map α :=
  (ModuleCat.extendRestrictScalarsAdj.{max u v r m, max u v r m, max u v r m}
      ((liftedSite.{u, v, r, m} X hX).O.obj.map f.op).hom).homEquiv_naturality_right_square
    ((evaluationLifted.{u, v, r, m} X V).map α) (restrictionMapLifted X hX G f)
    (restrictionMapLifted X hX F f) ((evaluationLifted.{u, v, r, m} X U).map α)
    (restrictionMapLifted_naturality X hX f α)

private noncomputable def canonicalMapNatTrans
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥) {U V : X.C} (f : U ⟶ V) :
    (evaluationLifted.{u, v, r, m} X V ⋙
      ModuleCat.extendScalars.{max u v r m, max u v r m, max u v r m}
        ((liftedSite.{u, v, r, m} X hX).O.obj.map f.op).hom) ⟶
      evaluationLifted.{u, v, r, m} X U where
  app F := canonicalMapLifted X hX F f
  naturality _ _ α := canonicalMapLifted_naturality X hX f α

private theorem evaluationLifted_map_exact
    (X : RingedSite.{u, v, r}) (hX : X.J = ⊥) (U : X.C)
    (S : ShortComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hS : S.Exact) :
    (S.map (evaluationLifted X U)).Exact := by
  have he := evaluation_map_exact X hX U S hS
  have hUL : ((S.map (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (op U))).map (ModuleCat.uliftFunctor.{max u v r, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))).Exact :=
    ModuleCat.uliftFunctor_map_exact _ _ he
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hUL ⊢
  exact hUL

/-- Quasi-coherent modules on a chaotic site with flat restrictions form a
weak Serre subcategory of all sheaves of modules. -/
@[stacks 0GZP]
public instance isQuasicoherentOnSite_isWeakSerreClass
    (X : RingedSite.{u, v, r}) [Fact (X.J = ⊥)]
    [Fact (∀ {U V : X.Cᵒᵖ} (a : V ⟶ U),
      RingHom.Flat (X.O.obj.map a).hom)] :
    ObjectProperty.IsWeakSerreClass
      (SheafOfModules.isQuasicoherentOnSite (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :
        ObjectProperty (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  let : HasSheafify X.J AddCommGrpCat.{m} := chaoticSheafify X Fact.out
  let : X.J.WEqualsLocallyBijective AddCommGrpCat.{m} :=
    chaoticWEqualsLocallyBijective X Fact.out
  let P : ObjectProperty (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    SheafOfModules.isQuasicoherentOnSite (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  rw [ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact P]
  constructor
  · refine ⟨0, (isQuasicoherent_iff_canonicalMapLifted_isIso X _ Fact.out).mpr fun U V f => ?_⟩
    have hzero := isZero_zero (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    exact ((ModuleCat.extendScalars.{max u v r m, max u v r m, max u v r m}
      ((liftedSite.{u, v, r, m} X Fact.out).O.obj.map f.op).hom).map_isZero
        ((evaluationLifted.{u, v, r, m} X V).map_isZero hzero)).isIso
      ((evaluationLifted.{u, v, r, m} X U).map_isZero hzero) _
  · refine fun S hS h₀ h₁ h₃ h₄ => (isQuasicoherent_iff_canonicalMapLifted_isIso X (S.obj' 2)
      Fact.out).mpr fun U V f => ?_
    let E := ModuleCat.extendScalars.{max u v r m, max u v r m, max u v r m}
      ((liftedSite.{u, v, r, m} X Fact.out).O.obj.map f.op).hom
    let F₁ := evaluationLifted.{u, v, r, m} X V ⋙ E
    let F₂ := evaluationLifted.{u, v, r, m} X U
    have hF₁ : ∀ T : ShortComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
        T.Exact → (T.map F₁).Exact := by
      intro T hT
      have hflat : RingHom.Flat (X.O.obj.map f.op).hom :=
        (inferInstance : Fact (∀ {U V : X.Cᵒᵖ} (a : V ⟶ U),
          RingHom.Flat (X.O.obj.map a).hom)).out f.op
      convert extendScalars_map_exact_lifted.{max u v r m, max u v r m}
        (f := ((liftedSite.{u, v, r, m} X Fact.out).O.obj.map f.op).hom)
        (liftedRestriction_flat.{u, v, r, m} X Fact.out f hflat) _
        (evaluationLifted_map_exact X Fact.out V T hT) using 1
      exact ShortComplex.map_comp T (evaluationLifted.{u, v, r, m} X V) E
    have hF₂ : ∀ T : ShortComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
        T.Exact → (T.map F₂).Exact := fun T hT => evaluationLifted_map_exact X Fact.out U T hT
    have hsource : ((F₁.mapComposableArrows 4).obj S).Exact :=
      composableArrows_map_exact F₁ S hS hF₁
    have htarget : ((F₂.mapComposableArrows 4).obj S).Exact :=
      composableArrows_map_exact F₂ S hS hF₂
    let η := canonicalMapNatTrans X Fact.out f
    have hiso : ∀ M : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
        M.IsQuasicoherentOnSite → IsIso (η.app M) := fun M hM =>
      (isQuasicoherent_iff_canonicalMapLifted_isIso X M Fact.out).mp hM f
    let ψ : ((F₁.mapComposableArrows 4).obj S) ⟶
        ((F₂.mapComposableArrows 4).obj S) :=
      ComposableArrows.homMk (fun i => η.app (S.obj i)) (by
        intro i hi
        simpa [F₁, F₂] using η.naturality (S.map' i (i + 1)))
    have hmid := CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
      hsource htarget ψ (by
        have := hiso _ h₀
        change Epi (η.app (S.obj' 0))
        infer_instance) (hiso _ h₁) (hiso _ h₃) (by
        have := hiso _ h₄
        change Mono (η.app (S.obj' 4))
        infer_instance)
    have hmid' : IsIso (η.app (S.obj' 2)) := by
      simpa [ψ, ComposableArrows.homMk] using hmid
    exact hmid'

end Stacks.Sheaves.ChaoticFlatQuasicoherent
