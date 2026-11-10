module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianUnderlyingSets
public import StacksFrontier.CategoryTheory.Sites.Sheafification.LocalRepresentatives

/-!
# Finite local constancy of a sheaf of modules over a finite ring

Let `(C, J)` be a site and let `Λ` be a **finite** ring. A sheaf of `Λ`-modules on `C` is finite
locally constant exactly when the sheaf of abelian groups underlying it is: the condition sees
only the underlying abelian sheaf.

## Main results

* `Stacks.ConstantSheaf.isFiniteLocallyConstant_moduleSheaf_of_forget`: a sheaf of `Λ`-modules
  whose underlying sheaf of sets is finite locally constant is itself finite locally constant.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_forgetModule`: the underlying sheaf of sets of a
  finite locally constant sheaf of modules is finite locally constant.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_forget₂Module`: the underlying abelian sheaf of a
  finite locally constant sheaf of modules is finite locally constant.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_moduleSheaf_iff_forget₂`: a sheaf of modules over
  a finite ring is finite locally constant if and only if its underlying abelian sheaf is.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5), part (3)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ConstantSheaf

universe v u r

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ]

/-! ### A locally bijective comparison with a constant presheaf -/

/-- A locally bijective map from a constant presheaf on `E` to a sheaf of modules `F` gives an
isomorphism of the constant sheaf on `E` with `F`. -/
public noncomputable def constantModuleSheafIsoOfLocallyBijective
    (E : ModuleCat.{max u v} Λ) (F : Sheaf J (ModuleCat.{max u v} Λ))
    (a : (Functor.const Cᵒᵖ).obj E ⟶ F.obj)
    (hinj : Presheaf.IsLocallyInjective J a)
    (hsurj : Presheaf.IsLocallySurjective J a) :
    (constantSheaf J (ModuleCat.{max u v} Λ)).obj E ≅ F := by
  have := hinj
  have := hsurj
  letI : J.PreservesSheafification (forget (ModuleCat.{max u v} Λ)) :=
    preservesSheafification_forget_moduleCat.{v, u, v} J Λ
  let f : (constantSheaf J (ModuleCat.{max u v} Λ)).obj E ⟶ F :=
    ObjectProperty.homMk (CategoryTheory.sheafifyLift J a F.property)
  have hf : CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj E) ≫ f.hom = a :=
    CategoryTheory.toSheafify_sheafifyLift J a F.property
  have hToSheafifySurj : Presheaf.IsLocallySurjective J
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj E)) :=
    Presheaf.isLocallySurjective_toSheafify' J _
  have : Sheaf.IsLocallyInjective f := by
    change Presheaf.IsLocallyInjective J f.hom
    apply (Presheaf.comp_isLocallyInjective_iff J
      (CategoryTheory.toSheafify J _) f.hom).mp
    rw [hf]
    infer_instance
  have : Sheaf.IsLocallySurjective f := by
    change Presheaf.IsLocallySurjective J f.hom
    apply (Presheaf.comp_isLocallySurjective_iff J
      (CategoryTheory.toSheafify J _) f.hom).mp
    rw [hf]
    infer_instance
  have := (Sheaf.isLocallyBijective_iff_isIso f).mp ⟨inferInstance, inferInstance⟩
  exact asIso f

/-- On a site with a terminal object `T`, a locally bijective map from a constant presheaf on a
finite set to the underlying presheaf of sets of a sheaf of modules, whose image over `T` is
closed under the module operations, makes the sheaf of modules isomorphic to a constant sheaf on
a finite module. -/
public theorem isConstant_moduleSheaf_of_finite_range
    (S : Sheaf J (ModuleCat.{max u v} Λ)) (A : Type (max u v)) [Finite A]
    (η : (Functor.const Cᵒᵖ).obj A ⟶ S.obj ⋙ forget (ModuleCat.{max u v} Λ))
    (hinj : Presheaf.IsLocallyInjective J η) (hsurj : Presheaf.IsLocallySurjective J η)
    {T : C} (hT : IsTerminal T)
    (hz : (0 : ToType (S.obj.obj (op T))) ∈ Set.range (η.app (op T)))
    (ha : ∀ x y : ToType (S.obj.obj (op T)), x ∈ Set.range (η.app (op T)) →
      y ∈ Set.range (η.app (op T)) → x + y ∈ Set.range (η.app (op T)))
    (hs : ∀ (c : Λ) (x : ToType (S.obj.obj (op T))), x ∈ Set.range (η.app (op T)) →
      c • x ∈ Set.range (η.app (op T))) :
    ∃ H : ModuleCat.{max u v} Λ, Finite (ToType H) ∧
      Nonempty ((constantSheaf J (ModuleCat.{max u v} Λ)).obj H ≅ S) := by
  classical
  have := hinj
  have := hsurj
  let H : Submodule Λ (ToType (S.obj.obj (op T))) :=
    { carrier := Set.range (η.app (op T))
      zero_mem' := hz
      add_mem' := ha _ _
      smul_mem' := hs }
  let q : A → H := fun a ↦ ⟨η.app (op T) a, ⟨a, rfl⟩⟩
  have hq : Function.Surjective q := fun ⟨_, a, ha⟩ ↦ ⟨a, Subtype.ext ha⟩
  have : Finite H := Finite.of_surjective q hq
  let ψ : (Functor.const Cᵒᵖ).obj (ModuleCat.of Λ H) ⟶ S.obj :=
    { app V := ModuleCat.ofHom ((S.obj.map (hT.from V.unop).op).hom.comp H.subtype)
      naturality V W f := by
        ext x
        change S.obj.map (hT.from W.unop).op x.val =
          S.obj.map f (S.obj.map (hT.from V.unop).op x.val)
        rw [← Functor.map_comp_apply,
          show (hT.from W.unop).op = (hT.from V.unop).op ≫ f from
            congrArg Quiver.Hom.op (hT.hom_ext _ _)] }
  let q' := (Functor.const Cᵒᵖ).map (TypeCat.ofHom q)
  let ψ' := Functor.whiskerRight ψ (forget (ModuleCat.{max u v} Λ))
  have hfac : q' ≫ ψ' = η := by
    ext V a
    exact (NatTrans.naturality_apply η (hT.from V.unop).op a).symm
  have : Presheaf.IsLocallySurjective J q' :=
    Presheaf.isLocallySurjective_of_surjective J q' (fun _ ↦ hq)
  have : Presheaf.IsLocallyInjective J (q' ≫ ψ') := hfac.symm ▸ inferInstance
  have : Presheaf.IsLocallySurjective J (q' ≫ ψ') := hfac.symm ▸ inferInstance
  have : Presheaf.IsLocallyInjective J ψ' :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J q' ψ'
  have : Presheaf.IsLocallySurjective J ψ' :=
    Presheaf.isLocallySurjective_of_isLocallySurjective J q' ψ'
  have : Presheaf.IsLocallyInjective J ψ :=
    (Presheaf.isLocallyInjective_forget_iff J ψ).mp inferInstance
  have : Presheaf.IsLocallySurjective J ψ :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J ψ).mpr inferInstance
  exact ⟨ModuleCat.of Λ H, inferInstance,
    ⟨constantModuleSheafIsoOfLocallyBijective J Λ _ S ψ inferInstance inferInstance⟩⟩

/-- A sheaf of sets on `J.over X` isomorphic to a constant sheaf on `A` receives a locally
bijective map from the constant presheaf on `A`. -/
public theorem exists_isLocallyBijective_of_iso_constantSheaf {X : C} {A : Type (max u v)}
    {G : Sheaf (J.over X) (Type (max u v))}
    (e : (constantSheaf (J.over X) (Type (max u v))).obj A ≅ G) :
    ∃ η : (Functor.const (Over X)ᵒᵖ).obj A ⟶ G.obj,
      Presheaf.IsLocallySurjective (J.over X) η ∧ Presheaf.IsLocallyInjective (J.over X) η := by
  have hIso : IsIso e.hom.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf (J.over X) (Type (max u v))).map e.hom))
  have heS : Presheaf.IsLocallySurjective (J.over X) e.hom.hom := inferInstance
  have heI : Presheaf.IsLocallyInjective (J.over X) e.hom.hom := inferInstance
  have htS : Presheaf.IsLocallySurjective (J.over X)
      (CategoryTheory.toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj A)) := inferInstance
  have htI : Presheaf.IsLocallyInjective (J.over X)
      (CategoryTheory.toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj A)) := inferInstance
  exact ⟨CategoryTheory.toSheafify (J.over X) _ ≫ e.hom.hom,
    @Presheaf.isLocallySurjective_comp _ _ (J.over X) _ _ _ _ _ _ _ _ _
      (CategoryTheory.toSheafify (J.over X) _) e.hom.hom htS heS,
    @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ (J.over X) _ _ _
      (CategoryTheory.toSheafify (J.over X) _) e.hom.hom htI heI⟩

/-- A locally bijective map from a constant presheaf on a finite set to a sheaf of modules on
`J.over X`, whose image over `W` is closed under the module operations, makes the restriction of
the sheaf to `W` finite constant. -/
public theorem exists_iso_constantSheaf_overPullback_of_range_closed
    (F : Sheaf J (ModuleCat.{max u v} Λ)) {X : C} (A : Type (max u v)) [Finite A]
    (η : (Functor.const (Over X)ᵒᵖ).obj A ⟶
      ((J.overPullback (ModuleCat.{max u v} Λ) X).obj F).obj ⋙ forget (ModuleCat.{max u v} Λ))
    (hInj : Presheaf.IsLocallyInjective (J.over X) η)
    (hSurj : Presheaf.IsLocallySurjective (J.over X) η) (W : Over X)
    (hz : ∃ a : A, η.app (op W) a = 0)
    (hadd : ∀ a b : A, ∃ c : A, η.app (op W) c = η.app (op W) a + η.app (op W) b)
    (hsmul : ∀ (c : Λ) (a : A), ∃ b : A, η.app (op W) b = c • η.app (op W) a) :
    ∃ E : ModuleCat.{max u v} Λ, Finite (ToType E) ∧
      Nonempty ((constantSheaf (J.over W.left) (ModuleCat.{max u v} Λ)).obj E ≅
        (J.overPullback (ModuleCat.{max u v} Λ) W.left).obj F) := by
  have hwS : Presheaf.IsLocallySurjective (J.over W.left)
      (Functor.whiskerLeft (Over.map W.hom).op η) :=
    Presheaf.isLocallySurjective_whisker (J.over W.left) (J.over X) (Over.map W.hom) η
  have hwI : Presheaf.IsLocallyInjective (J.over W.left)
      (Functor.whiskerLeft (Over.map W.hom).op η) :=
    Presheaf.isLocallyInjective_whisker (J.over W.left) (J.over X) (Over.map W.hom) η
  have he : (Functor.whiskerLeft (Over.map W.hom).op η).app
      (op (Over.mk (𝟙 W.left))) = η.app (op W) := by
    refine ConcreteCategory.ext_apply fun a ↦ ?_
    refine (NatTrans.naturality_apply η (Over.homMk (𝟙 W.left) (by simp) :
      (Over.map W.hom).obj (Over.mk (𝟙 W.left)) ⟶ W).op a).trans ?_
    simp only [Functor.comp_obj, Functor.comp_map,
      Functor.sheafPushforwardContinuous_obj_obj_map, Over.forget_obj, Over.map_obj_left,
      Over.mk_left, Quiver.Hom.unop_op, Over.forget_map, Over.homMk_left, op_id,
      CategoryTheory.Functor.map_id, TypeCat.ofHom_apply, Functor.const_obj_obj,
      Functor.op_obj]
    exact ConcreteCategory.id_apply _
  refine isConstant_moduleSheaf_of_finite_range (J.over W.left) Λ
    ((J.overPullback (ModuleCat.{max u v} Λ) W.left).obj F) A
    (Functor.whiskerLeft (Over.map W.hom).op η) hwI hwS Over.mkIdTerminal ?_ ?_ ?_
  · exact hz.imp fun _ h ↦ by rwa [he]
  · rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact (hadd a b).imp fun _ h ↦ by rwa [he]
  · rintro c x ⟨a, rfl⟩
    exact (hsmul c a).imp fun _ h ↦ by rwa [he]

/-! ### The two directions -/

/-- A sheaf of `Λ`-modules whose underlying sheaf of sets is finite locally constant is itself
finite locally constant, for `Λ` a finite ring. -/
public theorem isFiniteLocallyConstant_moduleSheaf_of_forget [Finite Λ]
    (F : Sheaf J (ModuleCat.{max u v} Λ))
    (hF : IsFiniteLocallyConstant J
      ((sheafCompose J (forget (ModuleCat.{max u v} Λ))).obj F)) :
    IsFiniteLocallyConstant J F := by
  classical
  refine ⟨fun U ↦ ?_⟩
  obtain ⟨I, X, f, hf, hloc⟩ := hF.exists_finite_cover U
  refine exists_cover_trans J (P := fun V ↦ ∃ E : ModuleCat.{max u v} Λ,
    Finite (ToType E) ∧ Nonempty ((constantSheaf (J.over V) (ModuleCat.{max u v} Λ)).obj E ≅
      (J.overPullback (ModuleCat.{max u v} Λ) V).obj F)) hf fun i ↦ ?_
  obtain ⟨A, hA, ⟨e⟩⟩ := hloc i
  have : Finite A := hA
  have : Fintype A := Fintype.ofFinite A
  have : Fintype Λ := Fintype.ofFinite Λ
  obtain ⟨η, hSurj, hInj⟩ : ∃ η : (Functor.const (Over (X i))ᵒᵖ).obj A ⟶
      ((J.overPullback (ModuleCat.{max u v} Λ) (X i)).obj F).obj ⋙
        forget (ModuleCat.{max u v} Λ),
      Presheaf.IsLocallySurjective (J.over (X i)) η ∧
        Presheaf.IsLocallyInjective (J.over (X i)) η :=
    exists_isLocallyBijective_of_iso_constantSheaf J e
  obtain ⟨L, W, p, hp, hrep⟩ := Stacks.Sheafification.exists_cover_representatives
    (D := Type (max u v)) (J.over (X i)) η (Over.mk (𝟙 (X i)))
    (fun j ↦ (Fintype.equivFin ((A × A) ⊕ ((Λ × A) ⊕ PUnit.{1}))).symm j |>.elim
      (fun ab ↦ η.app (op (Over.mk (𝟙 (X i)))) ab.1 + η.app (op (Over.mk (𝟙 (X i)))) ab.2)
      (Sum.elim (fun ca ↦ ca.1 • η.app (op (Over.mk (𝟙 (X i)))) ca.2) (fun _ ↦ 0)))
  refine ⟨L, fun l ↦ (W l).left, fun l ↦ (p l).left, ?_, fun l ↦ ?_⟩
  · rwa [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hp
  · have hr (z : (A × A) ⊕ ((Λ × A) ⊕ PUnit.{1})) :
        ∃ a : A, ((J.overPullback (ModuleCat.{max u v} Λ) (X i)).obj F).obj.map (p l).op
          (z.elim (fun ab ↦ η.app (op (Over.mk (𝟙 (X i)))) ab.1 +
              η.app (op (Over.mk (𝟙 (X i)))) ab.2)
            (Sum.elim (fun ca ↦ ca.1 • η.app (op (Over.mk (𝟙 (X i)))) ca.2) (fun _ ↦ 0))) =
          η.app (op (W l)) a := by
      obtain ⟨a, ha⟩ := (hrep l).2 (Fintype.equivFin ((A × A) ⊕ ((Λ × A) ⊕ PUnit.{1})) z)
      exact ⟨a, by rwa [Equiv.symm_apply_apply] at ha⟩
    have hc (a : A) : ((J.overPullback (ModuleCat.{max u v} Λ) (X i)).obj F).obj.map (p l).op
        (η.app (op (Over.mk (𝟙 (X i)))) a) = η.app (op (W l)) a :=
      (NatTrans.naturality_apply η (p l).op a).symm
    have hz : ∃ a : A, η.app (op (W l)) a = 0 := by
      obtain ⟨a, ha⟩ := hr (.inr (.inr PUnit.unit))
      exact ⟨a, by rw [← ha, Sum.elim_inr, Sum.elim_inr, map_zero]⟩
    have hadd : ∀ a b : A, ∃ c : A,
        η.app (op (W l)) c = η.app (op (W l)) a + η.app (op (W l)) b := fun a b ↦ by
      obtain ⟨c, h⟩ := hr (.inl (a, b))
      exact ⟨c, by rw [← h, Sum.elim_inl, map_add, hc, hc]⟩
    have hsmul : ∀ (c : Λ) (a : A), ∃ b : A,
        η.app (op (W l)) b = c • η.app (op (W l)) a := fun c a ↦ by
      obtain ⟨b, h⟩ := hr (.inr (.inl (c, a)))
      refine ⟨b, ?_⟩
      rw [← h, Sum.elim_inr, Sum.elim_inl, ← hc a]
      exact map_smul _ _ _
    exact exists_iso_constantSheaf_overPullback_of_range_closed J Λ F A η hInj hSurj (W l)
      hz hadd hsmul

/-- Forgetting the module structure preserves finite local constancy. -/
public theorem isFiniteLocallyConstant_forgetModule
    (F : Sheaf J (ModuleCat.{max u v} Λ)) (hF : IsFiniteLocallyConstant J F) :
    IsFiniteLocallyConstant J
      ((sheafCompose J (forget (ModuleCat.{max u v} Λ))).obj F) := by
  refine ⟨fun U ↦ ?_⟩
  obtain ⟨I, V, f, hf, hV⟩ := hF.exists_finite_cover U
  refine ⟨I, V, f, hf, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hV i
  refine ⟨(forget (ModuleCat.{max u v} Λ)).obj M, hM, ⟨?_⟩⟩
  let : (J.over (V i)).PreservesSheafification (forget (ModuleCat.{max u v} Λ)) :=
    preservesSheafification_forget_moduleCat.{v, max u v, v} (J.over (V i)) Λ
  exact (constantCommuteCompose (J.over (V i))
      (forget (ModuleCat.{max u v} Λ))).symm.app M ≪≫
    (sheafCompose (J.over (V i)) (forget (ModuleCat.{max u v} Λ))).mapIso e

/-- Forgetting the abelian group structure after the module structure is forgetting the module
structure. -/
public theorem sheafCompose_forget₂_forget
    (F : Sheaf J (ModuleCat.{max u v} Λ)) :
    (sheafCompose J (forget AddCommGrpCat.{max u v})).obj
        ((sheafCompose J (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v})).obj F) =
      (sheafCompose J (forget (ModuleCat.{max u v} Λ))).obj F := by
  refine ObjectProperty.FullSubcategory.ext ?_
  change F.obj ⋙ forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v} ⋙
    forget AddCommGrpCat.{max u v} = F.obj ⋙ forget (ModuleCat.{max u v} Λ)
  rw [HasForget₂.forget_comp]

/-- The underlying abelian sheaf of a finite locally constant sheaf of modules is finite locally
constant. -/
public theorem isFiniteLocallyConstant_forget₂Module
    (F : Sheaf J (ModuleCat.{max u v} Λ)) (hF : IsFiniteLocallyConstant J F) :
    IsFiniteLocallyConstant J
      ((sheafCompose J (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v})).obj F) := by
  refine isFiniteLocallyConstant_of_forget J _ ?_
  rw [sheafCompose_forget₂_forget]
  exact isFiniteLocallyConstant_forgetModule J Λ F hF

/-- A sheaf of modules over a finite ring is finite locally constant if and only if its
underlying abelian sheaf is. -/
public theorem isFiniteLocallyConstant_moduleSheaf_iff_forget₂ [Finite Λ]
    (F : Sheaf J (ModuleCat.{max u v} Λ)) :
    IsFiniteLocallyConstant J F ↔
      IsFiniteLocallyConstant J
        ((sheafCompose J (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v})).obj F) := by
  refine ⟨isFiniteLocallyConstant_forget₂Module J Λ F, fun h ↦ ?_⟩
  refine isFiniteLocallyConstant_moduleSheaf_of_forget J Λ F ?_
  rw [← sheafCompose_forget₂_forget J Λ F]
  exact isFiniteLocallyConstant_forget J _ h

end Stacks.ConstantSheaf

end
