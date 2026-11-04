module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianTerminal

/-!
# Maps out of a module cartesian over a terminal object on a cover-dense subcategory

Let `Gf : C ⥤ D` be a functor, `Rc` a presheaf of commutative rings on `D`, and `M₀`, `N₀`
presheaves of `Rc`-modules, read on `C` through `Gf` (`PresheafOfModules.pushforward`).  Let `K`
be a topology on `C` for which `N₀` read on `C` is a sheaf, let `A` be a cover-dense full
subcategory of `(C, K)` and `t` a terminal object of `C` lying in `A`.  If `M₀` is cartesian over
the image under `Gf` of every map to `t` from an object of `A`, then evaluation at `t` is a
bijection from the morphisms `M₀|_C ⟶ N₀|_C` onto the linear maps `M₀(t) ⟶ N₀(t)`.

Morphisms out of `M₀|_C` into the sheaf `N₀|_C` are morphisms on `A`, by cover-density
(`CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom`, linearity being local); on `A` the
object `t` is terminal and `M₀` is cartesian over every map to it, which is
`Stacks.PresheafOfModules.bijective_app_of_isTerminal`.

The case of interest is the slice `𝒳/x` of the fppf site of a category fibred in groupoids at an
object `x` lying over an affine scheme, with `A` its objects over affine schemes: there a
quasi-coherent module is cartesian between affine objects, so the sections over `x` of an
internal Hom out of it are the linear maps of sections over `x`.

## Main results

* `Stacks.PresheafOfModules.bijective_app_of_isTerminal_of_isCoverDense`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ v₁ u₂ v₂ r

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (K : GrothendieckTopology C) (Gf : C ⥤ D) {Rc : Dᵒᵖ ⥤ CommRingCat.{r}}
  (M₀ N₀ : _root_.PresheafOfModules.{r} (Rc ⋙ forget₂ CommRingCat RingCat))
  (A : ObjectProperty C) [A.ι.IsCoverDense K]

/-- **Evaluation at a terminal object is bijective on maps out of a module cartesian over every
map to it from a cover-dense full subcategory, into a sheaf.** -/
theorem bijective_app_of_isTerminal_of_isCoverDense
    (hN : Presheaf.IsSheaf K (Gf.op ⋙ N₀.presheaf))
    {t : C} (ht : IsTerminal t) (hAt : A t)
    (hM : ∀ V : C, A V → IsIso (restrictionBaseChange M₀ (Gf.map (ht.from V)).op)) :
    Function.Bijective (fun α :
        (_root_.PresheafOfModules.pushforward (F := Gf)
          (𝟙 (Gf.op ⋙ Rc ⋙ forget₂ CommRingCat RingCat))).obj M₀ ⟶
        (_root_.PresheafOfModules.pushforward (F := Gf)
          (𝟙 (Gf.op ⋙ Rc ⋙ forget₂ CommRingCat RingCat))).obj N₀ => α.app (op t)) := by
  let Rf := Rc ⋙ forget₂ CommRingCat RingCat
  let P := _root_.PresheafOfModules.pushforward (F := Gf) (𝟙 (Gf.op ⋙ Rf))
  let tA : A.FullSubcategory := ⟨t, hAt⟩
  let htA : IsTerminal tA := IsTerminal.ofUniqueHom
    (fun V => ObjectProperty.homMk (ht.from V.obj)) (fun V m => by ext : 1; exact ht.hom_ext _ _)
  let L := A.ι ⋙ Gf
  let MA : _root_.PresheafOfModules.{r} ((L.op ⋙ Rc) ⋙ forget₂ CommRingCat RingCat) :=
    (_root_.PresheafOfModules.pushforward₀ L Rf).obj M₀
  let NA : _root_.PresheafOfModules.{r} ((L.op ⋙ Rc) ⋙ forget₂ CommRingCat RingCat) :=
    (_root_.PresheafOfModules.pushforward₀ L Rf).obj N₀
  have hMA : ∀ V : A.FullSubcategory,
      IsIso (restrictionBaseChange (R := L.op ⋙ Rc) MA (htA.from V).op) := fun V => by
    have h := hM V.obj V.property
    rwa [← congrArg Gf.map (ht.hom_ext (A.ι.map (htA.from V)) (ht.from V.obj))] at h
  let res : (P.obj M₀ ⟶ P.obj N₀) → (MA ⟶ NA) := fun α =>
    { app := fun X => α.app (A.ι.op.obj X)
      naturality := fun f => α.naturality (A.ι.op.map f) }
  let ℱt : Sheaf K (Type r) := ⟨Gf.op ⋙ N₀.presheaf ⋙ forget AddCommGrpCat,
    Presheaf.isSheaf_comp_of_isSheaf K _ (forget AddCommGrpCat) hN⟩
  have hext : ∀ {U : C} (x y : N₀.obj (op (Gf.obj U))),
      (∀ (Y : A.FullSubcategory) (f : Y.obj ⟶ U),
        N₀.map (Gf.map f).op x = N₀.map (Gf.map f).op y) → x = y :=
    fun _ _ h => Functor.IsCoverDense.ext A.ι ℱt _ h
  have hres : Function.Bijective res := by
    refine ⟨fun α β h => ?_, fun w => ?_⟩
    · refine _root_.PresheafOfModules.hom_ext fun U => ?_
      ext m
      refine hext _ _ fun Y f => ?_
      have hc := congrArg (fun γ : MA ⟶ NA => γ.app (op Y) (M₀.map (Gf.map f).op m)) h
      exact (_root_.PresheafOfModules.naturality_apply α f.op m).symm.trans
        (hc.trans (_root_.PresheafOfModules.naturality_apply β f.op m))
    · let ℱ' : Sheaf K AddCommGrpCat.{r} := ⟨Gf.op ⋙ N₀.presheaf, hN⟩
      let u' : A.ι.op ⋙ (Gf.op ⋙ M₀.presheaf) ⟶ A.ι.op ⋙ ℱ'.obj :=
        (_root_.PresheafOfModules.toPresheaf _).map w
      let g := (Functor.IsCoverDense.restrictHomEquivHom (G := A.ι) (K := K)
        (ℱ := Gf.op ⋙ M₀.presheaf) (ℱ' := ℱ')) u'
      have hg : ∀ (Y : A.FullSubcategory) (m : M₀.obj (op (Gf.obj Y.obj))),
          g.app (op Y.obj) m = w.app (op Y) m := fun Y m =>
        congrArg (fun f => f m) (congrArg (fun s => (s.app (op Y)).hom)
          (Functor.IsCoverDense.sheafHom_restrict_eq (G := A.ι) (K := K)
            (ℱ := Gf.op ⋙ M₀.presheaf) (ℱ' := ℱ') u'))
      have hnat : ∀ {U V : C} (f : V ⟶ U) (m : M₀.obj (op (Gf.obj U))),
          g.app (op V) (M₀.map (Gf.map f).op m) = N₀.map (Gf.map f).op (g.app (op U) m) :=
        fun f m => NatTrans.naturality_apply g f.op m
      have hlin : ∀ (U : Cᵒᵖ) (c : Rf.obj (op (Gf.obj U.unop)))
          (m : M₀.obj (op (Gf.obj U.unop))),
          g.app U (c • m) = c • @id (N₀.obj (op (Gf.obj U.unop))) (g.app U m) := fun U c m => by
        refine hext _ _ fun Y f => ?_
        erw [N₀.map_smul, ← hnat f m, ← hnat f (c • m), M₀.map_smul, hg, hg,
          (w.app (op Y)).hom.map_smul]
        rfl
      refine ⟨_root_.PresheafOfModules.homMk (M₁ := P.obj M₀) (M₂ := P.obj N₀) g hlin, ?_⟩
      refine _root_.PresheafOfModules.hom_ext fun Y => ?_
      ext m
      exact hg Y.unop m
  exact (bijective_app_of_isTerminal (R := L.op ⋙ Rc) (N := NA) MA htA hMA).comp hres

/-- **Every linear map of sections over a terminal object is the component of a map**, in the
setting of `Stacks.PresheafOfModules.bijective_app_of_isTerminal_of_isCoverDense`. -/
theorem exists_app_eq_of_isTerminal_of_isCoverDense
    (hN : Presheaf.IsSheaf K (Gf.op ⋙ N₀.presheaf))
    {t : C} (ht : IsTerminal t) (hAt : A t)
    (hM : ∀ V : C, A V → IsIso (restrictionBaseChange M₀ (Gf.map (ht.from V)).op))
    (ψ : letI : Module (Rc.obj (op (Gf.obj t))) (M₀.obj (op (Gf.obj t))) :=
          inferInstanceAs (Module ((Rc ⋙ forget₂ CommRingCat RingCat).obj (op (Gf.obj t))) _)
        letI : Module (Rc.obj (op (Gf.obj t))) (N₀.obj (op (Gf.obj t))) :=
          inferInstanceAs (Module ((Rc ⋙ forget₂ CommRingCat RingCat).obj (op (Gf.obj t))) _)
        M₀.obj (op (Gf.obj t)) →ₗ[Rc.obj (op (Gf.obj t))] N₀.obj (op (Gf.obj t))) :
    ∃ α : (_root_.PresheafOfModules.pushforward (F := Gf)
          (𝟙 (Gf.op ⋙ Rc ⋙ forget₂ CommRingCat RingCat))).obj M₀ ⟶
        (_root_.PresheafOfModules.pushforward (F := Gf)
          (𝟙 (Gf.op ⋙ Rc ⋙ forget₂ CommRingCat RingCat))).obj N₀,
      ∀ m, α.app (op t) m = ψ m := by
  obtain ⟨α, hα⟩ := (bijective_app_of_isTerminal_of_isCoverDense K Gf M₀ N₀ A hN ht hAt hM).2
    (ModuleCat.ofHom
      { toFun := fun m => ψ m
        map_add' := ψ.map_add
        map_smul' := fun c m => ψ.map_smul c m })
  exact ⟨α, fun m => congrArg (fun f => f.hom m) hα⟩

end Stacks.PresheafOfModules
