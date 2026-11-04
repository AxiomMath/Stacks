module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization

/-!
# Internal Hom out of a finitely presented module on a ringed site

On a ringed site the internal Hom of Stacks 03EM carries colimits in its first variable to limits:
a finite coproduct of sheaves of modules to a product and a cokernel to a kernel, since the
restriction to every slice preserves colimits in a universe containing the site. Together with
`𝓗om(𝒪, G) = G` this exhibits the internal Hom out of the cokernel of a map between finite free
modules as the kernel of a map between finite products of copies of the target.

## Main results

* `AlgebraicGeometry.RingedSite.isLimitInternalHomSheafFan` and
  `AlgebraicGeometry.RingedSite.isLimitInternalHomSheafKernelFork`: internal Hom against `G`
  carries a finite coproduct to a product and a cokernel to a kernel.
* `AlgebraicGeometry.RingedSite.internalHomSheafULiftUnitIso`: `𝓗om(𝒪, G) ≅ G`, with the
  sections of `𝒪` raised to the universe of `G`.
* `AlgebraicGeometry.RingedSite.internalHomSheafULiftIso`: raising the universe of the sections
  of both arguments does not change the internal Hom.
* `AlgebraicGeometry.RingedSite.exists_internalHomSheaf_iso_kernel`: the internal Hom out of a
  cokernel of a map between finite free modules is a kernel of a map between finite products of
  copies of the target.
* `AlgebraicGeometry.RingedSite.internalHomSheafOverIso`: Stacks 0E8H for sheaves of modules on a
  ringed site.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u₁ v₁ r m

variable (Y : RingedSite.{u₁, v₁, r})

/-- **Internal Hom against `G` carries a finite coproduct of sheaves of modules in its first
variable to a product.** -/
noncomputable def isLimitInternalHomSheafFan {n : ℕ}
    {L P : SheafOfModules.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (G : SheafOfModules.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ι : Fin n → (L ⟶ P))
    (hP : IsColimit (Cofan.mk P ι)) :
    IsLimit (Fan.mk (internalHomSheaf Y P G) (fun i => internalHomPre Y (C := G) (ι i))) := by
  letI := (SheafOfModules.fullyFaithfulForget.{max u₁ v₁ r m}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).full
  letI := (SheafOfModules.fullyFaithfulForget.{max u₁ v₁ r m}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).faithful
  refine isLimitOfReflects
    (SheafOfModules.forget.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((isLimitMapConeFanMkEquiv _ _ _).symm ?_)
  refine PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X => ?_)
  refine isLimitOfReflects (forget _) ?_
  have : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        X.unop) :=
    have := Stacks.SheafOfModules.overFunctor_preservesColimits.{u₁, v₁, r, m}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) X.unop
    preservesColimitsOfSize_shrink _
  have hW := (isColimitMapCoconeCofanMkEquiv
    (SheafOfModules.overFunctor.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) X.unop)
      (fun _ => L) ι).1
      (isColimitOfPreserves _ hP)
  refine ((Types.isLimit_iff _).2 (fun s hs => ?_)).some
  let t : P.over X.unop ⟶ G.over X.unop :=
    Cofan.IsColimit.desc hW (fun i => ⟨s ⟨i⟩⟩)
  refine ⟨t.val, fun ⟨i⟩ => ?_, fun x hx => ?_⟩
  · exact congrArg SheafOfModules.Hom.val (Cofan.IsColimit.fac hW _ i)
  · have : (⟨x⟩ : P.over X.unop ⟶ G.over X.unop) = t :=
      Cofan.IsColimit.hom_ext hW _ _ (fun i => by
        refine (SheafOfModules.hom_ext ?_).trans (Cofan.IsColimit.fac hW _ i).symm
        exact hx ⟨i⟩)
    exact congrArg SheafOfModules.Hom.val this

/-- Precomposition with two composable morphisms whose composite vanishes is zero. -/
theorem internalHomPre_comp_internalHomPre_eq_zero
    {Q P N G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (a : Q ⟶ P) (b : P ⟶ N) (hab : a ≫ b = 0) :
    internalHomPre Y (C := G) b ≫ internalHomPre Y a = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext; intro U
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro g
  apply PresheafOfModules.hom_ext; intro V
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  let g' : (restrFun Y.O.obj U.unop).obj (valOf Y N) ⟶
      (restrFun Y.O.obj U.unop).obj (valOf Y G) := g
  have h : (a ≫ b).val.app (op V.unop.left) x = 0 := by rw [hab]; rfl
  exact (congrArg (g'.app V).hom h).trans (map_zero _)

/-- **Internal Hom against `G` carries a cokernel of sheaves of modules in its first variable to
a kernel.** -/
noncomputable def isLimitInternalHomSheafKernelFork
    {Q P N : SheafOfModules.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (G : SheafOfModules.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (a : Q ⟶ P) (b : P ⟶ N) (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab)) :
    IsLimit (KernelFork.ofι (internalHomPre Y (C := G) b)
      (internalHomPre_comp_internalHomPre_eq_zero Y a b hab)) := by
  letI := (SheafOfModules.fullyFaithfulForget.{max u₁ v₁ r m}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).full
  letI := (SheafOfModules.fullyFaithfulForget.{max u₁ v₁ r m}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).faithful
  letI : (SheafOfModules.forget.{max u₁ v₁ r m}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).PreservesZeroMorphisms :=
    ⟨fun _ _ => rfl⟩
  refine isLimitOfReflects
    (SheafOfModules.forget.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((KernelFork.isLimitMapConeEquiv _ _).symm ?_)
  refine PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X => ?_)
  refine isLimitOfReflects (forget _) ?_
  have : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        X.unop) :=
    have := Stacks.SheafOfModules.overFunctor_preservesColimits.{u₁, v₁, r, m}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) X.unop
    preservesColimitsOfSize_shrink _
  have : (SheafOfModules.overFunctor.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      X.unop).PreservesZeroMorphisms :=
    ⟨fun _ _ => rfl⟩
  have hW := isColimitCoforkMapOfIsColimit'
    (SheafOfModules.overFunctor.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) X.unop)
    hab hb
  refine ((Types.isLimit_iff _).2 (fun s hs => ?_)).some
  have h0 : (SheafOfModules.overFunctor.{max u₁ v₁ r m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      X.unop).map a ≫
      (show P.over X.unop ⟶ G.over X.unop from ⟨s .zero⟩) = 0 :=
    SheafOfModules.hom_ext <|
      (hs WalkingParallelPairHom.left).trans (hs WalkingParallelPairHom.right).symm
  let t := CokernelCofork.IsColimit.desc' hW _ h0
  refine ⟨t.1.val, ?_, fun x hx => ?_⟩
  · rintro (_ | _)
    · exact congrArg SheafOfModules.Hom.val t.2
    · refine Eq.trans ?_ (hs WalkingParallelPairHom.left)
      exact congrArg (fun k => (restrFun Y.O.obj X.unop).map a.val ≫ k)
        (congrArg SheafOfModules.Hom.val t.2)
  · have : (⟨x⟩ : N.over X.unop ⟶ G.over X.unop) = t.1 :=
      Cofork.IsColimit.hom_ext hW (SheafOfModules.hom_ext ((hx .zero).trans
        (congrArg SheafOfModules.Hom.val t.2).symm))
    exact congrArg SheafOfModules.Hom.val this

/-- The morphism `(O|_U)^{ulift} ⟶ G|_U` of presheaves of modules on the slice over `U` sending
a section `a` over `V ⟶ U` to `a • x|_V`, for a section `x` of `G` over `U`. -/
noncomputable def uliftUnitInternalHomSection
    (G : SheafOfModules.{max u₁ v₁ r} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (U : Y.C) (x : G.val.obj (op U)) :
    (restrFun Y.O.obj U).obj (valOf Y (SheafOfModules.uliftForPresentation.{_, _, _, _,
      max u₁ v₁ r} (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ⟶
      (restrFun Y.O.obj U).obj (valOf Y G) where
  app V := ModuleCat.homEquiv.symm
    { toFun := fun a => (show ((ORestr Y.O.obj U).obj V : Type r) from
          (show ULift.{max u₁ v₁ r} ((ORestr Y.O.obj U).obj V : Type r) from a).down) •
        (show (((restrFun Y.O.obj U).obj (valOf Y G)).obj V : Type (max u₁ v₁ r)) from
          G.val.map V.unop.hom.op x)
      map_add' := fun a b => add_smul _ _ _
      map_smul' := fun a b => mul_smul _ _ _ }
  naturality {V W} g := by
    ext a
    have h₁ : G.val.map W.unop.hom.op x =
        G.val.map g.unop.left.op (G.val.map V.unop.hom.op x) := by
      rw [← G.val.map_comp_apply, ← op_comp, Over.w g.unop]
    exact (congrArg (fun m => _ • m) h₁).trans (G.val.map_smul g.unop.left.op _ _).symm

/-- Evaluation of a section of `Hom(O^{ulift}, G)` over `U` at the section `1` over the identity
of `U`. -/
noncomputable def uliftUnitInternalHomEval
    (G : SheafOfModules.{max u₁ v₁ r} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (U : Y.Cᵒᵖ) (f : (restrFun Y.O.obj U.unop).obj (valOf Y
      (SheafOfModules.uliftForPresentation.{_, _, _, _, max u₁ v₁ r}
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ⟶
      (restrFun Y.O.obj U.unop).obj (valOf Y G)) : ((valOf Y G).obj U : Type (max u₁ v₁ r)) :=
  f.app (op (Over.mk (𝟙 U.unop)))
    (ULift.up (1 : (ORestr Y.O.obj U.unop).obj (op (Over.mk (𝟙 U.unop)))))

/-- A morphism `(O|_U)^{ulift} ⟶ G|_U` is determined by its value at `1` over the identity. -/
theorem uliftUnitInternalHomSection_eval
    (G : SheafOfModules.{max u₁ v₁ r} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (U : Y.Cᵒᵖ) (f : (restrFun Y.O.obj U.unop).obj (valOf Y
      (SheafOfModules.uliftForPresentation.{_, _, _, _, max u₁ v₁ r}
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ⟶
      (restrFun Y.O.obj U.unop).obj (valOf Y G)) :
    uliftUnitInternalHomSection Y G U.unop (uliftUnitInternalHomEval Y G U f) = f := by
  apply PresheafOfModules.hom_ext
  intro V
  ext a
  let a' : (ORestr Y.O.obj U.unop).obj V :=
    (show ULift.{max u₁ v₁ r} ((ORestr Y.O.obj U.unop).obj V : Type r) from a).down
  let one : ((restrFun Y.O.obj U.unop).obj (valOf Y
      (SheafOfModules.uliftForPresentation.{_, _, _, _, max u₁ v₁ r}
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))).obj V :=
    (show ULift.{max u₁ v₁ r} ((ORestr Y.O.obj U.unop).obj V : Type r) from ULift.up 1)
  let g : V.unop ⟶ Over.mk (𝟙 U.unop) := Over.homMk V.unop.hom (by simp)
  have hnat := PresheafOfModules.naturality_apply f g.op
    (ULift.up (1 : (ORestr Y.O.obj U.unop).obj (op (Over.mk (𝟙 U.unop)))))
  have h₁ : ((restrFun Y.O.obj U.unop).obj (valOf Y
      (SheafOfModules.uliftForPresentation.{_, _, _, _, max u₁ v₁ r}
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))).map g.op
      (ULift.up (1 : (ORestr Y.O.obj U.unop).obj (op (Over.mk (𝟙 U.unop))))) = one :=
    congrArg ULift.up (map_one ((Y.O.obj.map V.unop.hom.op).hom))
  rw [h₁] at hnat
  have h₂ : a = a' • one := congrArg ULift.up (mul_one a').symm
  refine Eq.trans ?_ (congrArg (f.app V).hom h₂).symm
  refine Eq.trans ?_ ((f.app V).hom.map_smul a' one).symm
  exact congrArg (fun m => a' • m) hnat.symm

/-- **Internal Hom out of the structure sheaf, with its sections raised to the universe of the
target, is the identity**: `Hom(O^{ulift}, G) ≅ G`, a section over `U` of the left side being
determined by its value at `1` over the identity of `U`. -/
noncomputable def internalHomSheafULiftUnitIso
    (G : SheafOfModules.{max u₁ v₁ r} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    internalHomSheaf Y (SheafOfModules.uliftForPresentation.{_, _, _, _, max u₁ v₁ r}
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) G ≅ G := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U => ?_) ?_)
  · let e : ((internalHom Y.O.obj (valOf Y (SheafOfModules.uliftForPresentation.{_, _, _, _,
          max u₁ v₁ r} (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
          (valOf Y G)).obj U :
          Type (max u₁ v₁ r)) ≃ₗ[(Oforget Y.O.obj).obj U] ((valOf Y G).obj U : Type _) :=
      { toFun := uliftUnitInternalHomEval Y G U
        invFun := uliftUnitInternalHomSection Y G U.unop
        left_inv := uliftUnitInternalHomSection_eval Y G U
        right_inv := fun x => by
          change (1 : (ORestr Y.O.obj U.unop).obj (op (Over.mk (𝟙 U.unop)))) •
            (show (((restrFun Y.O.obj U.unop).obj (valOf Y G)).obj
              (op (Over.mk (𝟙 U.unop))) : Type (max u₁ v₁ r)) from
              G.val.map (𝟙 U.unop).op x) = x
          rw [one_smul]
          change G.val.map (𝟙 U) x = x
          rw [G.val.map_id]
          rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => by
          have h : ((Oforget Y.O.obj).map (𝟙 U.unop).op).hom c = c := by
            rw [op_id, CategoryTheory.Functor.map_id]
            rfl
          exact congrArg (fun r : (Oforget Y.O.obj).obj U => r • uliftUnitInternalHomEval Y G U f)
            h }
    exact e.toModuleIso
  · intro U V g
    ext f
    change f.app (op (Over.mk (𝟙 V.unop ≫ g.unop)))
        (ULift.up (1 : (ORestr Y.O.obj U.unop).obj (op (Over.mk (𝟙 V.unop ≫ g.unop))))) =
      G.val.map g (uliftUnitInternalHomEval Y G U f)
    let k : Over.mk (𝟙 V.unop ≫ g.unop) ⟶ Over.mk (𝟙 U.unop) := Over.homMk g.unop (by simp)
    have hnat := PresheafOfModules.naturality_apply f k.op
      (ULift.up (1 : (ORestr Y.O.obj U.unop).obj (op (Over.mk (𝟙 U.unop)))))
    have h₁ : ((restrFun Y.O.obj U.unop).obj (valOf Y
        (SheafOfModules.uliftForPresentation.{_, _, _, _, max u₁ v₁ r}
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))).map k.op
        (ULift.up (1 : (ORestr Y.O.obj U.unop).obj (op (Over.mk (𝟙 U.unop))))) =
        ULift.up (1 : (ORestr Y.O.obj U.unop).obj (op (Over.mk (𝟙 V.unop ≫ g.unop)))) :=
      congrArg ULift.up (map_one ((Y.O.obj.map g).hom))
    rwa [h₁] at hnat

/-- Lowering the universe of a morphism between universe lifts of restricted presheaves of
modules. -/
noncomputable def internalHomULiftDown
    {A B : SheafOfModules.{r} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (U : Y.C)
    (α : (restrFun Y.O.obj U).obj (valOf Y
        (SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, max u₁ v₁ r} A)) ⟶
      (restrFun Y.O.obj U).obj (valOf Y
        (SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, max u₁ v₁ r} B))) :
    (restrFun Y.O.obj U).obj (valOf Y A) ⟶ (restrFun Y.O.obj U).obj (valOf Y B) where
  app V := ModuleCat.homEquiv.symm
    { toFun := fun x => (α.app V (ULift.up x)).down
      map_add' := fun x y => congrArg ULift.down (map_add (α.app V).hom (ULift.up x) (ULift.up y))
      map_smul' := fun c x => congrArg ULift.down (map_smul (α.app V).hom c (ULift.up x)) }
  naturality {V W} g := by
    ext x
    exact congrArg ULift.down (PresheafOfModules.naturality_apply α g (ULift.up x))

/-- Raising the universe of a morphism between restricted presheaves of modules. -/
noncomputable def internalHomULiftUp
    {A B : SheafOfModules.{r} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (U : Y.C)
    (α : (restrFun Y.O.obj U).obj (valOf Y A) ⟶ (restrFun Y.O.obj U).obj (valOf Y B)) :
    (restrFun Y.O.obj U).obj (valOf Y
        (SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, max u₁ v₁ r} A)) ⟶
      (restrFun Y.O.obj U).obj (valOf Y
        (SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, max u₁ v₁ r} B)) where
  app V := ModuleCat.homEquiv.symm
    { toFun := fun x => ULift.up (α.app V
        (show (((restrFun Y.O.obj U).obj (valOf Y A)).obj V : Type r) from
          (show ULift.{max u₁ v₁ r} (((restrFun Y.O.obj U).obj (valOf Y A)).obj V : Type r)
            from x).down))
      map_add' := fun x y => congrArg ULift.up (map_add (α.app V).hom
        (show (((restrFun Y.O.obj U).obj (valOf Y A)).obj V : Type r) from x.down)
        (show (((restrFun Y.O.obj U).obj (valOf Y A)).obj V : Type r) from y.down))
      map_smul' := fun c x => congrArg ULift.up (map_smul (α.app V).hom c
        (show (((restrFun Y.O.obj U).obj (valOf Y A)).obj V : Type r) from x.down)) }
  naturality {V W} g := by
    ext x
    exact congrArg ULift.up (PresheafOfModules.naturality_apply α g x.down)

/-- **Raising the universe of the sections of both arguments does not change the internal
Hom**: `Hom(A^{ulift}, B^{ulift}) ≅ Hom(A, B)`, sectionwise by `ULift.down` and `ULift.up`. -/
noncomputable def internalHomSheafULiftIso
    (A B : SheafOfModules.{r} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    internalHomSheaf Y (SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, max u₁ v₁ r} A)
      (SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, max u₁ v₁ r} B) ≅
      internalHomSheaf Y A B := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U => ?_) ?_)
  · let e : ((internalHom Y.O.obj
          (valOf Y (SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, max u₁ v₁ r} A))
          (valOf Y (SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, max u₁ v₁ r} B))).obj U :
            Type (max u₁ v₁ r)) ≃ₗ[(Oforget Y.O.obj).obj U]
          ((internalHom Y.O.obj (valOf Y A) (valOf Y B)).obj U : Type (max u₁ v₁ r)) :=
      { toFun := internalHomULiftDown Y U.unop
        invFun := internalHomULiftUp Y U.unop
        left_inv := fun α => by
          apply PresheafOfModules.hom_ext; intro V; ext x; rfl
        right_inv := fun α => by
          apply PresheafOfModules.hom_ext; intro V; ext x; rfl
        map_add' := fun α β => by
          apply PresheafOfModules.hom_ext; intro V; ext x; rfl
        map_smul' := fun c α => by
          apply PresheafOfModules.hom_ext; intro V; ext x; rfl }
    exact e.toModuleIso
  · intro U V g
    ext α
    apply PresheafOfModules.hom_ext; intro W; ext x; rfl

/-- **Internal Hom out of a finitely presented module is a kernel.** If `N` is the cokernel of a
morphism `Q ⟶ P` between finite coproducts of copies of the structure sheaf (with sections
raised to a universe containing the site), then `Hom(N, G)` is the kernel of a morphism
`G^n ⟶ G^k` between finite products of copies of `G`. -/
theorem exists_internalHomSheaf_iso_kernel {n k : ℕ}
    {P Q N : SheafOfModules.{max u₁ v₁ r} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (ι : Fin n → (SheafOfModules.uliftForPresentation.{_, _, _, _, max u₁ v₁ r}
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶ P))
    (hP : IsColimit (Cofan.mk P ι))
    (κ : Fin k → (SheafOfModules.uliftForPresentation.{_, _, _, _, max u₁ v₁ r}
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶ Q))
    (hQ : IsColimit (Cofan.mk Q κ))
    (a : Q ⟶ P) (b : P ⟶ N) (hab : a ≫ b = 0) (hb : IsColimit (CokernelCofork.ofπ b hab))
    (G : SheafOfModules.{max u₁ v₁ r} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ∃ f : ∏ᶜ (fun _ : Fin n => G) ⟶ ∏ᶜ (fun _ : Fin k => G),
      Nonempty (internalHomSheaf Y N G ≅ kernel f) := by
  let eP : internalHomSheaf Y P G ≅ ∏ᶜ (fun _ : Fin n => G) :=
    (isLimitInternalHomSheafFan.{u₁, v₁, r, r} Y G ι hP).conePointUniqueUpToIso
      (productIsProduct _) ≪≫ Pi.mapIso (fun _ => internalHomSheafULiftUnitIso Y G)
  let eQ : internalHomSheaf Y Q G ≅ ∏ᶜ (fun _ : Fin k => G) :=
    (isLimitInternalHomSheafFan.{u₁, v₁, r, r} Y G κ hQ).conePointUniqueUpToIso
      (productIsProduct _) ≪≫ Pi.mapIso (fun _ => internalHomSheafULiftUnitIso Y G)
  let eN : internalHomSheaf Y N G ≅ kernel (internalHomPre Y (C := G) a) :=
    (isLimitInternalHomSheafKernelFork.{u₁, v₁, r, r} Y G a b hab hb).conePointUniqueUpToIso
      (limit.isLimit _)
  exact ⟨eP.inv ≫ internalHomPre Y a ≫ eQ.hom,
    ⟨eN ≪≫ kernel.mapIso _ _ eP eQ (by simp)⟩⟩

/-- **Stacks 0E8H for sheaves of modules on a ringed site**: the restriction to the slice over `U`
of the internal Hom is the internal Hom of the restrictions. -/
noncomputable def internalHomSheafOverIso (U : Y.C)
    (F G : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (internalHomSheaf Y F G).over U ≅ internalHomSheaf (Y.over U) (F.over U) (G.over U) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (Stacks.SheafOfModules.InternalHom.internalHomOverIso Y U F G)

end AlgebraicGeometry.RingedSite

end
