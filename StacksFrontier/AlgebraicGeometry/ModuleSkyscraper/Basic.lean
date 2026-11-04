module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# The skyscraper sheaf of modules with varying scalars

Let `O` be a sheaf of rings on a topological space `X` and let `x` be a point of `X`. This
file constructs the *module skyscraper at `x`*, a functor

`i_{x,*} : ModuleCat O_x ⥤ SheafOfModules O`

from modules over the stalk `O_x` to sheaves of `O`-modules, and proves that it is right
adjoint to the module-valued stalk functor `AlgebraicGeometry.SheafOfModules.stalkFunctor O x`.
The sections of `i_{x,*} M` over `U` are the functions `PLift (x ∈ U) → M`, that is, `M` if
`x ∈ U` and the zero module otherwise, and a section `r` of `O` over `U` acts through its germ
at `x`.

## Main definitions

* `Stacks.ModuleSkyscraper.presheafObj` and `Stacks.ModuleSkyscraper.sheafObj`: the module
  skyscraper as a presheaf, respectively a sheaf, of `O`-modules.
* `Stacks.ModuleSkyscraper.functor`: the module skyscraper as a functor in the value module.
* `Stacks.ModuleSkyscraper.toStalk` and `Stacks.ModuleSkyscraper.stalkIso`: the germ of the
  constant global section, and the resulting isomorphism `M ≅ (i_{x,*} M)_x`.
* `Stacks.ModuleSkyscraper.ofStalkHom` and `Stacks.ModuleSkyscraper.homEquiv`: the morphism
  `P ⟶ i_{x,*} M` attached to a linear map `P_x ⟶ M`, and the resulting bijection.

## Main results

* `Stacks.ModuleSkyscraper.adjunction`:
  `AlgebraicGeometry.SheafOfModules.stalkFunctor O x ⊣ Stacks.ModuleSkyscraper.functor O x`,
  with the two `IsLeftAdjoint`/`IsRightAdjoint` instances it supplies.
* `Stacks.ModuleSkyscraper.isIso_toStalk`: the stalk of the module skyscraper at `x` is its
  value.

## References

* [Stacks Project, Tag 009A](https://stacks.math.columbia.edu/tag/009A)
* [Stacks Project, Tag 009C](https://stacks.math.columbia.edu/tag/009C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

universe u

namespace Stacks.ModuleSkyscraper

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-- The ring of scalars of the module skyscraper: the stalk of `O` at `x`. -/
abbrev Stalk : RingCat.{u} := TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x

/-- The germ map of the sheaf of rings at `x`, as a ring homomorphism. -/
abbrev germ (U : Opens X) (h : x ∈ U) : O.obj.obj (op U) →+* Stalk O x :=
  (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X) O.obj U x h).hom

variable (M : ModuleCat.{u} (Stalk O x))

/-- Scalar multiplication on `PLift (x ∈ U) → M`: a scalar `r ∈ O(U)` acts through its germ
at `x`. -/
local instance smulSections (U : (Opens X)ᵒᵖ) :
    SMul (O.obj.obj U) (PLift (x ∈ unop U) → M) :=
  ⟨fun r s h => germ O x (unop U) h.down r • s h⟩

/-- A scalar `r ∈ O(U)` acts on a section of the module skyscraper through its germ at `x`. -/
lemma smul_sections_apply {U : (Opens X)ᵒᵖ} (r : O.obj.obj U) (s : PLift (x ∈ unop U) → M)
    (h : PLift (x ∈ unop U)) : (r • s) h = germ O x (unop U) h.down r • s h := rfl

/-- The sections `PLift (x ∈ U) → M` of the module skyscraper over `U`, as a module over
`O(U)` acting through germs at `x`. -/
local instance moduleSections (U : (Opens X)ᵒᵖ) :
    Module (O.obj.obj U) (PLift (x ∈ unop U) → M) where
  one_smul s := by funext h; simp [smul_sections_apply]
  mul_smul r₁ r₂ s := by funext h; simp [smul_sections_apply, mul_smul]
  smul_zero r := by funext h; simp [smul_sections_apply]
  smul_add r s t := by funext h; simp [smul_sections_apply]
  add_smul r₁ r₂ s := by funext h; simp [smul_sections_apply, add_smul]
  zero_smul s := by funext h; simp [smul_sections_apply]

/-- The module skyscraper at `x` with value `M`, as a presheaf of `O`-modules: its sections
over `U` are the maps `PLift (x ∈ U) → M`, and `O(U)` acts through the germ at `x`. -/
def presheafObj : PresheafOfModules.{u} O.obj where
  obj U := ModuleCat.of (O.obj.obj U) (PLift (x ∈ unop U) → M)
  map {U V} i := ModuleCat.semilinearMapAddEquiv (O.obj.map i).hom _ _
    { toFun s := fun h => s ⟨i.unop.le h.down⟩
      map_add' s t := rfl
      map_smul' r s := by
        funext h
        simp only [smul_sections_apply]
        exact congrArg (· • s ⟨i.unop.le h.down⟩)
          (TopCat.Presheaf.germ_res_apply' (C := RingCat.{u}) O.obj i x h.down r).symm }

/-- Restriction along `i : U ⟶ V` in the module skyscraper is restriction of the index. -/
@[simp] lemma presheafObj_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : PLift (x ∈ unop U) → M) (h : PLift (x ∈ unop V)) :
    (presheafObj O x M).map i s h = s ⟨i.unop.le h.down⟩ := rfl

/-- The module skyscraper presheaf satisfies the sheaf condition. -/
lemma isSheaf_presheafObj :
    TopCat.Presheaf.IsSheaf (X := X) (presheafObj O x M).presheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have key : ∀ (i j : ι) (hi : x ∈ U i) (hj : x ∈ U j), sf i ⟨hi⟩ = sf j ⟨hj⟩ :=
    fun i j hi hj => congrFun (hsf i j) ⟨⟨hi, hj⟩⟩
  refine ⟨fun h => sf (Opens.mem_iSup.1 h.down).choose
      ⟨(Opens.mem_iSup.1 h.down).choose_spec⟩, fun j => funext fun h => ?_,
    fun t ht => funext fun h => ?_⟩
  · exact key _ j _ h.down
  · obtain ⟨j, hj⟩ := Opens.mem_iSup.1 h.down
    exact (congrFun (ht j) ⟨hj⟩).trans (key j _ hj _)

/-- The module skyscraper at `x` with value `M`, as a sheaf of `O`-modules. -/
def sheafObj : SheafOfModules.{u} O := ⟨presheafObj O x M, isSheaf_presheafObj O x M⟩

variable {M} {N : ModuleCat.{u} (Stalk O x)}

/-- The morphism of sheaves of modules induced by a linear map of values. -/
def sheafMap (f : M ⟶ N) : sheafObj O x M ⟶ sheafObj O x N :=
  ⟨{ app U := ModuleCat.ofHom
      { toFun s := fun h => f.hom (s h)
        map_add' s t := by funext h; exact map_add f.hom _ _
        map_smul' r s := by
          funext h
          simp only [smul_sections_apply]
          exact map_smul f.hom _ _ } }⟩

/-- `sheafMap O x f` applies `f` to the values of a section. -/
@[simp] lemma sheafMap_apply (f : M ⟶ N) (U : (Opens X)ᵒᵖ)
    (s : PLift (x ∈ unop U) → M) (h : PLift (x ∈ unop U)) :
    (sheafMap O x f).val.app U s h = f.hom (s h) := rfl

variable (M)

/-- **The module skyscraper at `x` with varying scalars.** The functor sending a module `M`
over the stalk `O_x` to the sheaf of `O`-modules whose sections over `U` are `M` if `x ∈ U`
and `0` elsewhere, with `O(U)` acting through the germ map at `x`. -/
def functor : ModuleCat.{u} (Stalk O x) ⥤ SheafOfModules.{u} O where
  obj M := sheafObj O x M
  map f := sheafMap O x f

/-- The stalk at `x` of a sheaf of `O`-modules, as a module over `O_x`. -/
abbrev stalkMod (P : SheafOfModules.{u} O) : ModuleCat.{u} (Stalk O x) :=
  AlgebraicGeometry.SheafOfModules.stalkObj O x P

/-- The germ at `x` of a section of the module skyscraper over an open containing `x`. -/
abbrev skyGerm (U : Opens X) (h : x ∈ U) (s : PLift (x ∈ U) → M) :
    stalkMod O x (sheafObj O x M) :=
  (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
    (presheafObj O x M).presheaf U x h).hom s

/-- The germ at `x` of the global section of the module skyscraper with constant value `m`. -/
abbrev topGerm (m : M) : stalkMod O x (sheafObj O x M) :=
  skyGerm O x M ⊤ trivial (fun _ => m)

/-- Every germ of the module skyscraper is the germ of a constant global section. -/
lemma skyGerm_eq_top (U : Opens X) (h : x ∈ U) (s : PLift (x ∈ U) → M) :
    skyGerm O x M U h s = topGerm O x M (s ⟨h⟩) :=
  TopCat.Presheaf.germ_res_apply' (C := AddCommGrpCat.{u}) (presheafObj O x M).presheaf
    (homOfLE (le_top : U ≤ ⊤)).op x h (fun _ => s ⟨h⟩)

/-- `topGerm O x M` is compatible with the action of germs of sections of `O`. -/
lemma topGerm_smul (V : (Opens X)ᵒᵖ) (hV : x ∈ unop V) (r₀ : O.obj.obj V) (m : M) :
    topGerm O x M (germ O x (unop V) hV r₀ • m) =
      germ O x (unop V) hV r₀ • topGerm O x M m := by
  calc topGerm O x M (germ O x (unop V) hV r₀ • m)
      = skyGerm O x M (unop V) hV (fun _ => germ O x (unop V) hV r₀ • m) :=
        (skyGerm_eq_top O x M (unop V) hV (fun _ => germ O x (unop V) hV r₀ • m)).symm
    _ = skyGerm O x M (unop V) hV (r₀ • (fun _ => m : PLift (x ∈ unop V) → M)) := rfl
    _ = germ O x (unop V) hV r₀ • skyGerm O x M (unop V) hV (fun _ => m) :=
        AlgebraicGeometry.SheafOfModules.germ_hom_smul O x (presheafObj O x M) (unop V) hV r₀ _
    _ = germ O x (unop V) hV r₀ • topGerm O x M m := by
        rw [skyGerm_eq_top O x M (unop V) hV (fun _ => m)]

/-- The canonical `O_x`-linear map from `M` to the stalk at `x` of its skyscraper: a value `m`
goes to the germ of the global section constantly equal to `m`. -/
def toStalkLinear : M →ₗ[Stalk O x] stalkMod O x (sheafObj O x M) where
  toFun m := topGerm O x M m
  map_add' m₁ m₂ := map_add _ _ _
  map_smul' r m := by
    obtain ⟨V, hV, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := RingCat.{u}) O.obj r
    exact topGerm_smul O x M (op V) hV r₀ m

/-- The canonical map `M ⟶ (i_{x,*} M)_x`, as a morphism of `O_x`-modules. -/
def toStalk : M ⟶ stalkMod O x (sheafObj O x M) := ModuleCat.ofHom (toStalkLinear O x M)

/-- `toStalk O x M` sends `m` to the germ of the constant global section with value `m`. -/
@[simp] lemma toStalk_apply (m : M) : (toStalk O x M).hom m = topGerm O x M m := rfl

/-- The canonical map `M ⟶ (i_{x,*} M)_x` is an isomorphism. -/
instance isIso_toStalk : IsIso (toStalk O x M) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun m m' hm ↦ ?_, fun t ↦ ?_⟩
  · obtain ⟨W, hW, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u})
      (presheafObj O x M).presheaf (U := ⊤) (V := ⊤) x trivial trivial
      (fun _ => m) (fun _ => m') hm
    exact congrFun heq ⟨hW⟩
  · obtain ⟨U, h, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
      (presheafObj O x M).presheaf t
    exact ⟨s ⟨h⟩, (skyGerm_eq_top O x M U h s).symm⟩

/-- **The stalk of the module skyscraper is its value.** The germ of the constant global
section is an isomorphism `M ≅ (i_{x,*} M)_x` of `O_x`-modules. -/
def stalkIso : M ≅ stalkMod O x (sheafObj O x M) := asIso (toStalk O x M)

/-- The inverse of `stalkIso O x M` sends the germ of the constant section `m` back to `m`. -/
lemma stalkIso_inv_topGerm (m : M) : (stalkIso O x M).inv.hom (topGerm O x M m) = m :=
  ConcreteCategory.congr_hom (stalkIso O x M).hom_inv_id m

/-- The germ at `x` of a section of a sheaf of `O`-modules. -/
abbrev modGerm (P : SheafOfModules.{u} O) (U : Opens X) (h : x ∈ U) (s : P.val.obj (op U)) :
    stalkMod O x P :=
  (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) P.val.presheaf U x h).hom s

variable {M} (P : SheafOfModules.{u} O)

/-- The morphism `P ⟶ i_{x,*} M` attached to an `O_x`-linear map `P_x ⟶ M`: a section over
`U` is sent to the constant function with value the image of its germ. -/
def ofStalkHom (ψ : stalkMod O x P ⟶ M) : P ⟶ sheafObj O x M :=
  ⟨{ app U := ModuleCat.ofHom
      { toFun s := fun h => ψ.hom (modGerm O x P (unop U) h.down s)
        map_add' s t := by
          funext h
          exact (congrArg ψ.hom (map_add _ s t)).trans (map_add ψ.hom _ _)
        map_smul' r s := by
          funext h
          exact (congrArg ψ.hom (AlgebraicGeometry.SheafOfModules.germ_hom_smul O x P.val
            (unop U) h.down r s)).trans (map_smul ψ.hom _ _) }
     naturality := by
       intro U V i
       ext s
       funext h
       exact congrArg ψ.hom
         (TopCat.Presheaf.germ_res_apply' (C := AddCommGrpCat.{u}) P.val.presheaf i x h.down s) }⟩

/-- `ofStalkHom O x P ψ` sends a section to the constant function with value `ψ` of its germ. -/
@[simp] lemma ofStalkHom_apply (ψ : stalkMod O x P ⟶ M) (U : (Opens X)ᵒᵖ)
    (s : P.val.obj U) (h : PLift (x ∈ unop U)) :
    (ofStalkHom O x P ψ).val.app U s h = ψ.hom (modGerm O x P (unop U) h.down s) := rfl

/-- The stalk map of a morphism `P ⟶ i_{x,*} M` sends the germ of `s` to the germ of its
image. -/
lemma stalkFunctor_map_modGerm (φ : P ⟶ sheafObj O x M) (U : Opens X) (h : x ∈ U)
    (s : P.val.obj (op U)) :
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).map φ).hom (modGerm O x P U h s) =
      skyGerm O x M U h (φ.val.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) U x h
    ((PresheafOfModules.toPresheaf O.obj).map φ.val) s

/-- The hom-set bijection `Hom_{O_x}(P_x, M) ≃ Hom_O(P, i_{x,*} M)`. -/
def homEquiv :
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).obj P ⟶ M) ≃
      (P ⟶ (functor O x).obj M) where
  toFun ψ := ofStalkHom O x P ψ
  invFun φ := (AlgebraicGeometry.SheafOfModules.stalkFunctor O x).map φ ≫ (stalkIso O x M).inv
  left_inv ψ := by
    ext t
    obtain ⟨U, h, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
      P.val.presheaf t
    exact (congrArg (stalkIso O x M).inv.hom
        (stalkFunctor_map_modGerm O x P (ofStalkHom O x P ψ) U h s)).trans
      ((congrArg (stalkIso O x M).inv.hom
          (skyGerm_eq_top O x M U h ((ofStalkHom O x P ψ).val.app (op U) s))).trans
        (stalkIso_inv_topGerm O x M (ψ.hom (modGerm O x P U h s))))
  right_inv φ := by
    ext U s
    funext h
    exact (congrArg (stalkIso O x M).inv.hom
        (stalkFunctor_map_modGerm O x P φ (unop U) h.down s)).trans
      ((congrArg (stalkIso O x M).inv.hom
          (skyGerm_eq_top O x M (unop U) h.down (φ.val.app (op (unop U)) s))).trans
        (stalkIso_inv_topGerm O x M ((φ.val.app (op (unop U)) s) ⟨h.down⟩)))

/-- **The module skyscraper at `x` is right adjoint to the module-valued stalk at `x`.**
The functor `M ↦ i_{x,*} M` from `O_x`-modules to sheaves of `O`-modules is right adjoint to
`AlgebraicGeometry.SheafOfModules.stalkFunctor O x`. -/
def adjunction :
    AlgebraicGeometry.SheafOfModules.stalkFunctor O x ⊣ functor O x :=
  Adjunction.mkOfHomEquiv
    { homEquiv P M := homEquiv O x P (M := M)
      homEquiv_naturality_left_symm := fun {_ _ M₀} f g =>
        (congrArg (· ≫ (stalkIso O x M₀).inv)
            ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).map_comp f g)).trans
          (Category.assoc _ _ _)
      homEquiv_naturality_right f g := by
        ext U s
        funext h
        rfl }

/-- The module skyscraper functor is a right adjoint. -/
instance : (functor O x).IsRightAdjoint := (adjunction O x).isRightAdjoint

/-- The module-valued stalk functor is a left adjoint. -/
instance : (AlgebraicGeometry.SheafOfModules.stalkFunctor O x).IsLeftAdjoint :=
  (adjunction O x).isLeftAdjoint

end Stacks.ModuleSkyscraper
