module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafLocalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre
public import StacksCore.Tactic.StacksAttribute

/-!
# Closure properties of the finite type locally constant sheaves of modules

Let `(C, J)` be a site and `Λ` a left Noetherian ring, not assumed commutative. The finite type
locally constant sheaves of `Λ`-modules,
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf`, contain `0` and are closed under
kernels and cokernels; granted closure under extensions, they form a weak Serre subcategory of
`Mod(C, Λ)`.

## Main definitions

* `Stacks.ConstantSheaf.mapPullbackConstantSheafIso`: the constant sheaf commutes with
  relocalization, `M̲|_{C/V} = M̲` for a morphism `V ⟶ U` read on `C/V ⥤ C/U`.
* `Stacks.ConstantSheaf.IsConstantFGOver`: `F` becomes, on `C/V`, the constant sheaf on a
  finitely generated module.
* `Stacks.ConstantSheaf.trivSieve`: the sieve of arrows into `U` whose source trivializes `F`.
* `Stacks.ConstantSheaf.IsConstantHomOver`: on `C/Z`, the morphism `f` is the morphism of
  constant sheaves attached to a map of finitely generated modules, together with the two
  trivializations.
* `Stacks.ConstantSheaf.constantHomSieve`: the sieve of arrows into `U` whose source satisfies
  the previous condition.

## Main results

* `Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat`: for presheaves of `Λ`-modules in a
  universe containing the site, `J.W` is local bijectivity.
* `Stacks.ConstantSheaf.containsZero_isFiniteTypeLocallyConstantModuleSheaf`: the zero sheaf is
  finite type locally constant.
* `Stacks.ConstantSheaf.constantHomSieve_mem`: over an object trivializing both `F` and `G`, the
  arrows on which `f` is a constant morphism cover.
* `Stacks.ConstantSheaf.isClosedUnderKernels_isFiniteTypeLocallyConstantModuleSheaf` and
  `Stacks.ConstantSheaf.isClosedUnderCokernels_isFiniteTypeLocallyConstantModuleSheaf`: closure
  under kernels and cokernels.
* `Stacks.ConstantSheaf.isWeakSerreClass_of_isClosedUnderExtensions`: granted closure under
  extensions, the finite type locally constant sheaves form a weak Serre subcategory.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace Stacks.ConstantSheaf

universe v u w r x

/-! ### Additivity of restriction along a continuous functor of sites -/

section Additive

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  (F : C ⥤ D) (A : Type*) [Category A] [Preadditive A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]

/-- Restriction of sheaves along a continuous functor of sites is additive. -/
instance additive_sheafPushforwardContinuous :
    (F.sheafPushforwardContinuous A J K).Additive where
  map_add := rfl

end Additive

section Restriction

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The constant sheaf commutes with relocalization: for a morphism `f : V ⟶ U` of the site,
the restriction along `Over.map f : C/V ⥤ C/U` of the constant sheaf on `C/U` attached to `M` is
the constant sheaf on `C/V` attached to `M`. -/
noncomputable def mapPullbackConstantSheafIso (A : Type*) [Category A] {U V : C} (f : V ⟶ U)
    [HasWeakSheafify (J.over V) A] [HasWeakSheafify (J.over U) A]
    [∀ (G : (Over V)ᵒᵖ ⥤ A), (Over.map f).op.HasPointwiseRightKanExtension G] :
    constantSheaf (J.over V) A ≅
      constantSheaf (J.over U) A ⋙ J.overMapPullback A f :=
  Functor.isoWhiskerLeft (Functor.const (Over U)ᵒᵖ)
    ((Over.map f).pushforwardContinuousSheafificationCompatibility A (J.over V) (J.over U))

section Component

variable (A : Type*) [Category A] {U V : C} (f : V ⟶ U)
  [HasWeakSheafify (J.over V) A] [HasWeakSheafify (J.over U) A]
  [∀ (G : (Over V)ᵒᵖ ⥤ A), (Over.map f).op.HasPointwiseRightKanExtension G]

/-- The component of `Stacks.ConstantSheaf.mapPullbackConstantSheafIso` at a single object, with
its result type in the uncomposed spelling `j^{-1}(M̲)` rather than
`(constantSheaf ⋙ j^{-1})(M)`. -/
noncomputable def mapPullbackConstantSheafApp (M : A) :
    (constantSheaf (J.over V) A).obj M ≅
      (J.overMapPullback A f).obj ((constantSheaf (J.over U) A).obj M) :=
  (mapPullbackConstantSheafIso J A f).app M

/-- Naturality of `Stacks.ConstantSheaf.mapPullbackConstantSheafApp` in the module. -/
theorem mapPullbackConstantSheafApp_naturality {M N : A} (ψ : M ⟶ N) :
    (constantSheaf (J.over V) A).map ψ ≫ (mapPullbackConstantSheafApp J A f N).hom =
      (mapPullbackConstantSheafApp J A f M).hom ≫
        (J.overMapPullback A f).map ((constantSheaf (J.over U) A).map ψ) :=
  (mapPullbackConstantSheafIso J A f).hom.naturality ψ

end Component

end Restriction

/-! ### Sheafification is locally bijective at a module universe containing the site -/

section LocallyBijective

open Presheaf GrothendieckTopology GrothendieckTopology.Plus

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The map to the plus construction is locally surjective, for presheaves of types in any
universe containing the site. -/
theorem isLocallySurjective_toPlus (P : Cᵒᵖ ⥤ Type (max u v w)) :
    IsLocallySurjective J (J.toPlus P) where
  imageSieve_mem x := by
    obtain ⟨S, x, rfl⟩ := exists_rep x
    refine J.superset_covering (fun Y f hf => ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using!
      x.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. }

/-- The map to the plus construction is locally injective, for presheaves of types in any
universe containing the site. -/
theorem isLocallyInjective_toPlus (P : Cᵒᵖ ⥤ Type (max u v w)) :
    IsLocallyInjective J (J.toPlus P) where
  equalizerSieve_mem {X} x y h := by
    rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact J.superset_covering (fun Y f hf => congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2

/-- Sheafification of presheaves of types is locally surjective, in any universe containing the
site. -/
theorem isLocallySurjective_plusPlus (P : Cᵒᵖ ⥤ Type (max u v w)) :
    IsLocallySurjective J (J.toSheafify P) := by
  have h₁ := isLocallySurjective_toPlus J P
  have h₂ := isLocallySurjective_toPlus J (J.plusObj P)
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  exact isLocallySurjective_comp (J := J) (J.toPlus P) (J.toPlus (J.plusObj P))

/-- Sheafification of presheaves of types is locally injective, in any universe containing the
site. -/
theorem isLocallyInjective_plusPlus (P : Cᵒᵖ ⥤ Type (max u v w)) :
    IsLocallyInjective J (J.toSheafify P) := by
  have h₁ := isLocallyInjective_toPlus J P
  have h₂ := isLocallyInjective_toPlus J (J.plusObj P)
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  exact isLocallyInjective_comp (J := J) (J.toPlus P) (J.toPlus (J.plusObj P))

variable (Λ : Type r) [Ring Λ]

/-- Sheafification of presheaves of `Λ`-modules commutes with the forgetful functor to types, at a
module universe containing the site. -/
theorem preservesSheafification_forget_moduleCat :
    J.PreservesSheafification (forget (ModuleCat.{max u v w} Λ)) := by
  have h₁ := ModuleCat.hasLimitsOfSize.{max u v, max u v, max u v w, r} (R := Λ)
  have h₂ : ∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ
      (forget (ModuleCat.{max u v w} Λ)) := fun X =>
    have := preservesColimitsOfShape_forget_addCommGrp.{u, v, w} J X
    Limits.comp_preservesColimitsOfShape
      (forget₂ (ModuleCat.{max u v w} Λ) AddCommGrpCat.{max u v w})
      (forget AddCommGrpCat.{max u v w})
  rw [preservesSheafification_iff_of_adjunctions_of_hasSheafCompose _ _
    (plusPlusAdjunction J (ModuleCat.{max u v w} Λ)) (plusPlusAdjunction J (Type (max u v w)))]
  infer_instance

/-- Sheafification of presheaves of `Λ`-modules is locally surjective, at a module universe
containing the site. -/
theorem isLocallySurjective_toSheafify_moduleCat (P : Cᵒᵖ ⥤ ModuleCat.{max u v w} Λ) :
    IsLocallySurjective J (CategoryTheory.toSheafify J P) := by
  have hp := preservesSheafification_forget_moduleCat.{v, u, w} J Λ
  have h := isLocallySurjective_plusPlus.{v, u, w} J (P ⋙ forget (ModuleCat.{max u v w} Λ))
  rw [isLocallySurjective_iff_whisker_forget,
    ← sheafComposeIso_hom_fac, ← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

/-- Sheafification of presheaves of `Λ`-modules is locally injective, at a module universe
containing the site. -/
theorem isLocallyInjective_toSheafify_moduleCat (P : Cᵒᵖ ⥤ ModuleCat.{max u v w} Λ) :
    IsLocallyInjective J (CategoryTheory.toSheafify J P) := by
  have hp := preservesSheafification_forget_moduleCat.{v, u, w} J Λ
  have h := isLocallyInjective_plusPlus.{v, u, w} J (P ⋙ forget (ModuleCat.{max u v w} Λ))
  rw [← isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

/-- `J.W` is local bijectivity for presheaves of `Λ`-modules at a module universe containing the
site. -/
instance wEqualsLocallyBijective_moduleCat :
    J.WEqualsLocallyBijective (ModuleCat.{max u v w} Λ) := by
  have h₁ := isLocallySurjective_toSheafify_moduleCat.{v, u, w} J Λ
  have h₂ := isLocallyInjective_toSheafify_moduleCat.{v, u, w} J Λ
  exact WEqualsLocallyBijective.mk' J (ModuleCat.{max u v w} Λ)

end LocallyBijective

/-! ### Local triviality as a sieve -/

section TrivSieve

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type r) [Ring Λ]

/-- `F` becomes, after restriction to the slice site `C/V`, the constant sheaf attached to a
finitely generated `Λ`-module. -/
def IsConstantFGOver (V : C) (F : Sheaf J (ModuleCat.{max u v w} Λ)) : Prop :=
  ∃ E : ModuleCat.{max u v w} Λ, ModuleCat.isFG Λ E ∧
    Nonempty ((constantSheaf (J.over V) (ModuleCat.{max u v w} Λ)).obj E ≅
      (J.overPullback (ModuleCat.{max u v w} Λ) V).obj F)

/-- `F` is finite type locally constant if and only if every object is covered by a family of
objects over each of which `F` is the constant sheaf on a finitely generated module. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_iff
    (F : Sheaf J (ModuleCat.{max u v w} Λ)) :
    IsFiniteTypeLocallyConstantModuleSheaf J Λ F ↔
      ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
        Sieve.ofArrows V f ∈ J U ∧ ∀ i, IsConstantFGOver J Λ (V i) F :=
  Iff.rfl

variable {J Λ}

/-- Local triviality is inherited by every object lying over a trivializing one. -/
theorem IsConstantFGOver.restrict {U V : C} (g : V ⟶ U)
    {F : Sheaf J (ModuleCat.{max u v w} Λ)} (h : IsConstantFGOver J Λ U F) :
    IsConstantFGOver J Λ V F := by
  obtain ⟨E, hE, ⟨φ⟩⟩ := h
  exact ⟨E, hE, ⟨(mapPullbackConstantSheafIso J (ModuleCat.{max u v w} Λ) g).app E ≪≫
    (J.overMapPullback (ModuleCat.{max u v w} Λ) g).mapIso φ⟩⟩

variable (J Λ)

/-- The trivializing sieve: the arrows into `U` whose source trivializes `F`. -/
def trivSieve (F : Sheaf J (ModuleCat.{max u v w} Λ)) (U : C) : Sieve U where
  arrows V _ := IsConstantFGOver J Λ V F
  downward_closed h g := h.restrict g

variable {J Λ}

/-- An arrow `g : V ⟶ U` lies in the trivializing sieve if and only if `V` trivializes `F`. -/
@[simp]
theorem mem_trivSieve_iff {F : Sheaf J (ModuleCat.{max u v w} Λ)} {U V : C} (g : V ⟶ U) :
    (trivSieve J Λ F U) g ↔ IsConstantFGOver J Λ V F :=
  Iff.rfl

/-- Pulling the trivializing sieve back along any arrow gives the trivializing sieve of the
source. -/
theorem trivSieve_pullback {F : Sheaf J (ModuleCat.{max u v w} Λ)} {U V : C} (g : V ⟶ U) :
    (trivSieve J Λ F U).pullback g = trivSieve J Λ F V := rfl

/-- `F` is locally constant of finite type exactly when every object is covered by its
trivializing sieve. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_iff_trivSieve_mem
    (F : Sheaf J (ModuleCat.{max u v w} Λ)) :
    IsFiniteTypeLocallyConstantModuleSheaf J Λ F ↔ ∀ U : C, trivSieve J Λ F U ∈ J U := by
  refine ⟨fun hF U => ?_, fun hF U => ?_⟩
  · obtain ⟨I, V, f, hcov, h⟩ := hF U
    refine J.superset_covering ?_ hcov
    rw [Sieve.generate_le_iff]
    rintro Y g ⟨i⟩
    exact h i
  · obtain ⟨I, V, f, hVf⟩ := Sieve.exists_eq_ofArrows (trivSieve J Λ F U)
    exact ⟨I, V, f, hVf ▸ hF U, fun i =>
      show (trivSieve J Λ F U) (f i) from hVf ▸ Sieve.ofArrows_mk V f i⟩

/-- If every member of some covering sieve of `U` is covered by its own trivializing sieve, then
so is `U`. -/
theorem trivSieve_mem_of_cover {F : Sheaf J (ModuleCat.{max u v w} Λ)} {U : C} {S : Sieve U}
    (hS : S ∈ J U) (h : ∀ ⦃Y : C⦄ (g : Y ⟶ U), S g → trivSieve J Λ F Y ∈ J Y) :
    trivSieve J Λ F U ∈ J U :=
  J.transitive hS _ (fun _ g hg => h g hg)

end TrivSieve

/-! ### The zero sheaf -/

section Zero

open ZeroObject

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type r) [Ring Λ]

/-- A zero module is finitely generated. -/
theorem isFG_of_isZero {X : ModuleCat.{x} Λ} (h : IsZero X) : ModuleCat.isFG Λ X := by
  have hsub : ∀ m : X, m = 0 := fun m => by
    simpa using ConcreteCategory.congr_hom (h.eq_of_src (𝟙 X) (0 : X ⟶ X)) m
  rw [ModuleCat.isFG_iff, Module.finite_def]
  exact ⟨∅, le_antisymm le_top fun m _ => hsub m ▸ zero_mem _⟩

/-- Every object of the site trivializes the zero sheaf. -/
theorem isConstantFGOver_zero (V : C) :
    IsConstantFGOver J Λ V (0 : Sheaf J (ModuleCat.{max u v w} Λ)) :=
  ⟨0, isFG_of_isZero Λ (isZero_zero _),
    ⟨(constantSheaf (J.over V) (ModuleCat.{max u v w} Λ)).mapZeroObject ≪≫
    ((J.overPullback (ModuleCat.{max u v w} Λ) V).mapZeroObject).symm⟩⟩

/-- The zero sheaf is locally constant of finite type. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_zero :
    IsFiniteTypeLocallyConstantModuleSheaf J Λ (0 : Sheaf J (ModuleCat.{max u v w} Λ)) := by
  rw [isFiniteTypeLocallyConstantModuleSheaf_iff_trivSieve_mem]
  exact fun U => J.superset_covering (fun Y g _ => isConstantFGOver_zero J Λ Y) (J.top_mem U)

/-- The finite type locally constant sheaves contain a zero object. -/
instance containsZero_isFiniteTypeLocallyConstantModuleSheaf :
    ObjectProperty.ContainsZero (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ) where
  exists_zero := ⟨0, isZero_zero _, isFiniteTypeLocallyConstantModuleSheaf_zero J Λ⟩

end Zero

/-! ### The local description of a morphism -/

section Morphism

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type r) [Ring Λ]
variable {F G : Sheaf J (ModuleCat.{max u v w} Λ)}

/-- After restriction to the slice site `C/Z`, the morphism `f` is the morphism of constant
sheaves attached to a map of finitely generated `Λ`-modules, together with the two
trivializations. -/
def IsConstantHomOver (Z : C) (f : F ⟶ G) : Prop :=
  ∃ (E E' : ModuleCat.{max u v w} Λ) (ψ : E ⟶ E'), ModuleCat.isFG Λ E ∧ ModuleCat.isFG Λ E' ∧
    ∃ (α : (constantSheaf (J.over Z) (ModuleCat.{max u v w} Λ)).obj E ≅
        (J.overPullback (ModuleCat.{max u v w} Λ) Z).obj F)
      (β : (constantSheaf (J.over Z) (ModuleCat.{max u v w} Λ)).obj E' ≅
        (J.overPullback (ModuleCat.{max u v w} Λ) Z).obj G),
      α.hom ≫ (J.overPullback (ModuleCat.{max u v w} Λ) Z).map f =
        (constantSheaf (J.over Z) (ModuleCat.{max u v w} Λ)).map ψ ≫ β.hom

variable {J Λ}

/-- If `f` is a constant morphism over `Z`, then `Z` trivializes the source of `f`. -/
theorem IsConstantHomOver.source {Z : C} {f : F ⟶ G} (h : IsConstantHomOver J Λ Z f) :
    IsConstantFGOver J Λ Z F := by
  obtain ⟨E, _, _, hE, _, α, _, _⟩ := h
  exact ⟨E, hE, ⟨α⟩⟩

/-- If `f` is a constant morphism over `Z`, then `Z` trivializes the target of `f`. -/
theorem IsConstantHomOver.target {Z : C} {f : F ⟶ G} (h : IsConstantHomOver J Λ Z f) :
    IsConstantFGOver J Λ Z G := by
  obtain ⟨_, E', _, _, hE', _, β, _⟩ := h
  exact ⟨E', hE', ⟨β⟩⟩

variable (J Λ)

/-- A trivialization of `F` over `U` restricted to an object `Z` lying over `U`, with target
spelled `j_Z^{-1} F` rather than `j_q^{-1} j_U^{-1} F`. -/
noncomputable def restrictTrivIso {U Z : C} (q : Z ⟶ U) (E : ModuleCat.{max u v w} Λ)
    (α : (constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).obj E ≅
      (J.overPullback (ModuleCat.{max u v w} Λ) U).obj F) :
    (constantSheaf (J.over Z) (ModuleCat.{max u v w} Λ)).obj E ≅
      (J.overPullback (ModuleCat.{max u v w} Λ) Z).obj F :=
  (mapPullbackConstantSheafApp J (ModuleCat.{max u v w} Λ) q E).trans
    ((J.overMapPullback (ModuleCat.{max u v w} Λ) q).mapIso α)

variable {J Λ}

/-- The square exhibiting `f` as a constant morphism over `U`, restricted along `q : Z ⟶ U`,
in the relocalization spelling `j_q^{-1}`. -/
theorem restrict_square {U Z : C} (q : Z ⟶ U) {f : F ⟶ G} {E E' : ModuleCat.{max u v w} Λ}
    (ψ : E ⟶ E')
    {α : (constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).obj E ≅
      (J.overPullback (ModuleCat.{max u v w} Λ) U).obj F}
    {β : (constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).obj E' ≅
      (J.overPullback (ModuleCat.{max u v w} Λ) U).obj G}
    (sq : (J.overMapPullback (ModuleCat.{max u v w} Λ) q).map
        (α.hom ≫ (J.overPullback (ModuleCat.{max u v w} Λ) U).map f) =
      (J.overMapPullback (ModuleCat.{max u v w} Λ) q).map
        ((constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).map ψ ≫ β.hom)) :
    ((mapPullbackConstantSheafApp J (ModuleCat.{max u v w} Λ) q E).hom ≫
        (J.overMapPullback (ModuleCat.{max u v w} Λ) q).map α.hom) ≫
      (J.overMapPullback (ModuleCat.{max u v w} Λ) q).map
        ((J.overPullback (ModuleCat.{max u v w} Λ) U).map f) =
      (constantSheaf (J.over Z) (ModuleCat.{max u v w} Λ)).map ψ ≫
        ((mapPullbackConstantSheafApp J (ModuleCat.{max u v w} Λ) q E').hom ≫
          (J.overMapPullback (ModuleCat.{max u v w} Λ) q).map β.hom) := by
  rw [Category.assoc, ← Functor.map_comp, sq, Functor.map_comp, ← Category.assoc,
    ← mapPullbackConstantSheafApp_naturality, Category.assoc]

/-- The local description of a morphism is inherited by every object lying over one where it
holds. -/
theorem IsConstantHomOver.restrict {U Z : C} (q : Z ⟶ U) {f : F ⟶ G}
    (h : IsConstantHomOver J Λ U f) : IsConstantHomOver J Λ Z f := by
  obtain ⟨E, E', ψ, hE, hE', α, β, sq⟩ := h
  exact ⟨E, E', ψ, hE, hE', restrictTrivIso J Λ q E α, restrictTrivIso J Λ q E' β,
    restrict_square q ψ (congrArg (J.overMapPullback (ModuleCat.{max u v w} Λ) q).map sq)⟩

variable (J Λ)

/-- The sieve on which a morphism is constant: the arrows `p : Z ⟶ U` such that `f` becomes,
after restriction to `C/Z`, the morphism of constant sheaves attached to a map of finitely
generated modules. -/
def constantHomSieve (f : F ⟶ G) (U : C) : Sieve U where
  arrows Z _ := IsConstantHomOver J Λ Z f
  downward_closed h g := h.restrict g

variable [IsNoetherianRing Λ]

/-- If `F` and `G` both become constant with finitely generated values after restriction to
`C/Y₀`, then the arrows on which `f` becomes the morphism of constant sheaves attached to a map of
modules cover `Y₀`. -/
@[sga "4 IX 2.1" "(ii), special case"]
theorem constantHomSieve_mem (f : F ⟶ G) {Y₀ : C}
    (hF : IsConstantFGOver J Λ Y₀ F) (hG : IsConstantFGOver J Λ Y₀ G) :
    constantHomSieve J Λ f Y₀ ∈ J Y₀ := by
  obtain ⟨E, hE, ⟨α₀⟩⟩ := hF
  obtain ⟨E', hE', ⟨β₀⟩⟩ := hG
  have hfin : Module.Finite Λ (E : Type (max u v w)) := hE
  have : Module.FinitePresentation Λ (E : Type (max u v w)) :=
    Module.finitePresentation_of_finite Λ _
  set ξ : (constantSheaf (J.over Y₀) (ModuleCat.{max u v w} Λ)).obj E ⟶
      (constantSheaf (J.over Y₀) (ModuleCat.{max u v w} Λ)).obj E' :=
    α₀.hom ≫ (J.overPullback (ModuleCat.{max u v w} Λ) Y₀).map f ≫ β₀.inv with hξ
  obtain ⟨I, V, g, hcov, hloc⟩ :=
    exists_cover_app_eq_constantSheaf_map (J.over Y₀) E E' ξ (Over.mk (𝟙 Y₀))
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hcov
  refine J.superset_covering ?_ hcov
  rw [Sieve.generate_le_iff]
  rintro Z p ⟨i⟩
  obtain ⟨ψ, hψ⟩ := hloc i
  have hleft : (g i).left = (V i).hom := by simpa using Over.w (g i)
  have hres : (J.overMapPullback (ModuleCat.{max u v w} Λ) (V i).hom).map ξ =
      (J.overMapPullback (ModuleCat.{max u v w} Λ) (V i).hom).map
        ((constantSheaf (J.over Y₀) (ModuleCat.{max u v w} Λ)).map ψ) :=
    Sheaf.hom_ext (NatTrans.ext (funext fun T =>
      hψ ((Over.map (V i).hom).obj T.unop) (Over.homMk T.unop.hom)))
  have key : IsConstantHomOver J Λ (V i).left f := by
    refine ⟨E, E', ψ, hE, hE', restrictTrivIso J Λ (V i).hom E α₀,
      restrictTrivIso J Λ (V i).hom E' β₀, restrict_square (V i).hom ψ ?_⟩
    have h₁ : α₀.hom ≫ (J.overPullback (ModuleCat.{max u v w} Λ) Y₀).map f = ξ ≫ β₀.hom := by
      rw [hξ, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h₁, Functor.map_comp, hres, ← Functor.map_comp]
  exact hleft ▸ key

end Morphism

/-! ### Exactness of the two functors involved -/

section Exactness

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type r) [Ring Λ]

/-- Restriction to a slice site preserves finite limits. -/
instance preservesFiniteLimits_overPullback (V : C) :
    PreservesFiniteLimits (J.overPullback (ModuleCat.{max u v w} Λ) V) := by
  have := (Adjunction.ofIsRightAdjoint
    (J.overPullback (ModuleCat.{max u v w} Λ) V)).rightAdjoint_preservesLimits
  infer_instance

/-- Restriction to a slice site preserves finite colimits. -/
@[ega "0 4.3.2" "partial"]
instance preservesFiniteColimits_overPullback (V : C) :
    PreservesFiniteColimits (J.overPullback (ModuleCat.{max u v w} Λ) V) := by
  have := ((Over.forget V).sheafAdjunctionCocontinuous (ModuleCat.{max u v w} Λ)
    (J.over V) J).leftAdjoint_preservesColimits
  infer_instance

/-- The constant sheaf functor on a slice site preserves finite colimits. -/
instance preservesFiniteColimits_constantSheaf_over (V : C) :
    PreservesFiniteColimits (constantSheaf (J.over V) (ModuleCat.{max u v w} Λ)) := by
  have := (constantSheafAdj (J.over V) (ModuleCat.{max u v w} Λ)
    (Over.mkIdTerminal (X := V))).leftAdjoint_preservesColimits
  infer_instance

variable [IsNoetherianRing Λ]

/-- Over a Noetherian ring, the kernel of a map of finitely generated modules is finitely
generated. -/
theorem isFG_kernel {E E' : ModuleCat.{x} Λ} (hE : ModuleCat.isFG Λ E) (ψ : E ⟶ E') :
    ModuleCat.isFG Λ (Limits.kernel ψ) := by
  have : Module.Finite Λ (E : Type x) := hE
  rw [ModuleCat.isFG_iff]
  exact Module.Finite.of_injective (Limits.kernel.ι ψ).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

omit [IsNoetherianRing Λ] in
/-- The cokernel of a map of finitely generated modules is finitely generated. -/
theorem isFG_cokernel {E E' : ModuleCat.{x} Λ} (hE' : ModuleCat.isFG Λ E') (ψ : E ⟶ E') :
    ModuleCat.isFG Λ (Limits.cokernel ψ) := by
  have : Module.Finite Λ (E' : Type x) := hE'
  rw [ModuleCat.isFG_iff]
  exact Module.Finite.of_surjective (Limits.cokernel.π ψ).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

variable {J Λ} {F G : Sheaf J (ModuleCat.{max u v w} Λ)}

/-- If `f` is a constant morphism over `Z`, then `Z` trivializes the kernel of `f`. -/
theorem IsConstantHomOver.kernel {Z : C} {f : F ⟶ G} (h : IsConstantHomOver J Λ Z f) :
    IsConstantFGOver J Λ Z (Limits.kernel f) := by
  obtain ⟨E, E', ψ, hE, hE', α, β, sq⟩ := h
  exact ⟨Limits.kernel ψ, isFG_kernel Λ hE ψ,
    ⟨Limits.PreservesKernel.iso (constantSheaf (J.over Z) (ModuleCat.{max u v w} Λ))
        (f := ψ) ≪≫
      Limits.kernel.mapIso ((constantSheaf (J.over Z) (ModuleCat.{max u v w} Λ)).map ψ)
        ((J.overPullback (ModuleCat.{max u v w} Λ) Z).map f) α β sq.symm ≪≫
      (Limits.PreservesKernel.iso (J.overPullback (ModuleCat.{max u v w} Λ) Z) (f := f)).symm⟩⟩

omit [IsNoetherianRing Λ] in
/-- If `f` is a constant morphism over `Z`, then `Z` trivializes the cokernel of `f`. -/
theorem IsConstantHomOver.cokernel {Z : C} {f : F ⟶ G} (h : IsConstantHomOver J Λ Z f) :
    IsConstantFGOver J Λ Z (Limits.cokernel f) := by
  obtain ⟨E, E', ψ, hE, hE', α, β, sq⟩ := h
  exact ⟨Limits.cokernel ψ, isFG_cokernel Λ hE' ψ,
    ⟨Limits.PreservesCokernel.iso (constantSheaf (J.over Z) (ModuleCat.{max u v w} Λ))
        (f := ψ) ≪≫
      Limits.cokernel.mapIso ((constantSheaf (J.over Z) (ModuleCat.{max u v w} Λ)).map ψ)
        ((J.overPullback (ModuleCat.{max u v w} Λ) Z).map f) α β sq.symm ≪≫
      (Limits.PreservesCokernel.iso (J.overPullback (ModuleCat.{max u v w} Λ) Z) (f := f)).symm⟩⟩

end Exactness

/-! ### Closure under kernels and cokernels -/

section Closure

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type r) [Ring Λ] [IsNoetherianRing Λ]
variable {F G : Sheaf J (ModuleCat.{max u v w} Λ)}

/-- For `F` and `G` locally constant of finite type, every object of the site is covered by
objects over which `f` is the morphism of constant sheaves attached to a map of finitely generated
modules. -/
@[sga "4 IX 2.1" "(ii), special case"]
theorem constantHomSieve_mem_of_isFiniteType (f : F ⟶ G)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf J Λ F)
    (hG : IsFiniteTypeLocallyConstantModuleSheaf J Λ G) (U : C) :
    constantHomSieve J Λ f U ∈ J U := by
  rw [isFiniteTypeLocallyConstantModuleSheaf_iff_trivSieve_mem] at hF hG
  exact J.transitive (J.intersection_covering (hF U) (hG U)) _
    (fun _ p hp => constantHomSieve_mem J Λ f hp.1 hp.2)

/-- If every constant morphism over `Z` makes `Z` trivialize `X`, then `X` is finite type locally
constant, for `X` built from a morphism of finite type locally constant sheaves. -/
private theorem isFiniteTypeLocallyConstantModuleSheaf_of_isConstantHomOver
    {X : Sheaf J (ModuleCat.{max u v w} Λ)} (f : F ⟶ G)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf J Λ F)
    (hG : IsFiniteTypeLocallyConstantModuleSheaf J Λ G)
    (h : ∀ {Z : C}, IsConstantHomOver J Λ Z f → IsConstantFGOver J Λ Z X) :
    IsFiniteTypeLocallyConstantModuleSheaf J Λ X := by
  rw [isFiniteTypeLocallyConstantModuleSheaf_iff_trivSieve_mem]
  exact fun U => J.superset_covering (fun _ _ => h)
    (constantHomSieve_mem_of_isFiniteType J Λ f hF hG U)

/-- The kernel of a morphism of finite type locally constant sheaves is finite type locally
constant. -/
@[sga "4 IX 2.1" "(ii), kernel assertion"]
theorem isFiniteTypeLocallyConstantModuleSheaf_kernel (f : F ⟶ G)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf J Λ F)
    (hG : IsFiniteTypeLocallyConstantModuleSheaf J Λ G) :
    IsFiniteTypeLocallyConstantModuleSheaf J Λ (Limits.kernel f) :=
  isFiniteTypeLocallyConstantModuleSheaf_of_isConstantHomOver J Λ f hF hG IsConstantHomOver.kernel

/-- The cokernel of a morphism of finite type locally constant sheaves is finite type locally
constant. -/
@[sga "4 IX 2.1" "(ii), cokernel assertion"]
theorem isFiniteTypeLocallyConstantModuleSheaf_cokernel (f : F ⟶ G)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf J Λ F)
    (hG : IsFiniteTypeLocallyConstantModuleSheaf J Λ G) :
    IsFiniteTypeLocallyConstantModuleSheaf J Λ (Limits.cokernel f) :=
  isFiniteTypeLocallyConstantModuleSheaf_of_isConstantHomOver J Λ f hF hG IsConstantHomOver.cokernel

/-- Finite type locally constant sheaves are closed under kernels. -/
instance isClosedUnderKernels_isFiniteTypeLocallyConstantModuleSheaf :
    ObjectProperty.IsClosedUnderKernels
      (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ) where
  kernels_le := by
    rintro X ⟨f, k, hk, hf⟩
    exact ObjectProperty.prop_of_iso _
      (Limits.IsLimit.conePointUniqueUpToIso (Limits.kernelIsKernel f) hk)
      (isFiniteTypeLocallyConstantModuleSheaf_kernel J Λ f hf.1 hf.2)

/-- Finite type locally constant sheaves are closed under cokernels. -/
instance isClosedUnderCokernels_isFiniteTypeLocallyConstantModuleSheaf :
    ObjectProperty.IsClosedUnderCokernels
      (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ) where
  cokernels_le := by
    rintro X ⟨f, k, hk, hf⟩
    exact ObjectProperty.prop_of_iso _
      (Limits.IsColimit.coconePointUniqueUpToIso (Limits.cokernelIsCokernel f) hk)
      (isFiniteTypeLocallyConstantModuleSheaf_cokernel J Λ f hf.1 hf.2)

/-- Granted closure under extensions, the finite type locally constant sheaves of `Λ`-modules
form a weak Serre subcategory. -/
theorem isWeakSerreClass_of_isClosedUnderExtensions
    [ObjectProperty.IsClosedUnderExtensions
      (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ)] :
    ObjectProperty.IsWeakSerreClass
      (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ) where

end Closure

end Stacks.ConstantSheaf

end
