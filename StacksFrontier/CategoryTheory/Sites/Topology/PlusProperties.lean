module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Properties of the plus construction

Stacks tag 00ZH, for presheaves of sets on a site `(C, J)`.  The plus construction
`F⁺` together with its natural map `ℓ : F ⟶ F⁺` is a functor on presheaves and `ℓ` is
natural in `F` (parts 1-3).  The construction preserves componentwise injectivity
(part 4), because the colimit over covers defining it is filtered and its transition maps
are the multiequalizer maps induced by `α`.  Finally, every section of `F⁺` over `U` comes,
on some covering sieve `S` of `U`, from a morphism `S.functor ⟶ F` pushed through `ℓ`
(part 5).

The construction itself is Mathlib's: `F⁺` is `CategoryTheory.GrothendieckTopology.plusObj`,
`ℓ` is `GrothendieckTopology.toPlus`, `α⁺` is `GrothendieckTopology.plusMap`, and the
endofunctor is `GrothendieckTopology.plusFunctor`.  Parts 1-3 are the functor laws and the
naturality of `ℓ` for those, so they are stated here directly against the Mathlib
declarations; parts 4 and 5 are proved below, Mathlib having no injectivity-preservation
statement for `plusMap` and no sieve-level form of the local representability.
-/

@[expose] public section

open CategoryTheory CategoryTheory.GrothendieckTopology Opposite

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-! ### Helpers for Statement 4 -/

/-- Componentwise action of `J.diagramNatTrans α U` via `Meq.equiv`. -/
lemma diagramNatTrans_app_meqEquiv_coord
    {F G : Cᵒᵖ ⥤ Type u} (α : F ⟶ G)
    (U : C) (𝒰 : J.Cover U)
    (x : (J.diagram F U).obj (op 𝒰)) (I : 𝒰.Arrow) :
    ((Meq.equiv G 𝒰) ((J.diagramNatTrans α U).app (op 𝒰) x) : Meq G 𝒰) I =
      α.app (op I.Y) (((Meq.equiv F 𝒰) x : Meq F 𝒰) I) := by
  change Limits.multiequalizer (𝒰.index F) at x
  rw [diagramNatTrans_app]
  change (Limits.Multiequalizer.lift (𝒰.index G) (Limits.multiequalizer (𝒰.index F))
        (fun a => Limits.Multiequalizer.ι (𝒰.index F) a ≫ α.app (op a.Y)) _
        ≫ Limits.Multiequalizer.ι (𝒰.index G) I) x = _
  exact ConcreteCategory.congr_hom (Limits.Multiequalizer.lift_ι (I := 𝒰.index G) _ _ _ I) x

/-- Componentwise injectivity is preserved by `J.diagramNatTrans`. -/
lemma diagram_map_injective_of_app_injective
    {F G : Cᵒᵖ ⥤ Type u} (α : F ⟶ G)
    (hα : ∀ U : Cᵒᵖ, Function.Injective (α.app U))
    (U : C) (𝒰op : (J.Cover U)ᵒᵖ) :
    Function.Injective ((J.diagramNatTrans α U).app 𝒰op) := by
  obtain ⟨𝒰⟩ := 𝒰op
  intro x y hxy
  apply (Meq.equiv F 𝒰).injective
  apply Meq.ext
  intro I
  apply hα (op I.Y)
  rw [← diagramNatTrans_app_meqEquiv_coord J α U 𝒰 x I,
      ← diagramNatTrans_app_meqEquiv_coord J α U 𝒰 y I, hxy]

/-- Filtered `Type u`-colimits preserve componentwise injectivity. -/
lemma filtered_colim_inj_of_componentwise_inj
    {K : Type u} [SmallCategory K] [IsFiltered K]
    {D₁ D₂ : K ⥤ Type u} (η : D₁ ⟶ D₂)
    (hη : ∀ k : K, Function.Injective (η.app k)) :
    Function.Injective (Limits.colim.map η) := by
  intro x y hxy
  obtain ⟨j₁, a₁, rfl⟩ :=
    Limits.Types.jointly_surjective _ (Limits.colimit.isColimit D₁) x
  obtain ⟨j₂, a₂, rfl⟩ :=
    Limits.Types.jointly_surjective _ (Limits.colimit.isColimit D₁) y
  simp only [Limits.colimit.cocone_ι] at hxy ⊢
  have hι : ∀ (j : K) (a : D₁.obj j), Limits.colim.map η (Limits.colimit.ι D₁ j a) =
      Limits.colimit.ι D₂ j (η.app j a) := fun j a =>
    congrArg (fun (f : D₁.obj j ⟶ Limits.colimit D₂) =>
      CategoryTheory.ConcreteCategory.hom f a) (Limits.colimit.ι_map η j)
  rw [hι, hι] at hxy
  obtain ⟨k, f, g, heq⟩ := (CategoryTheory.Limits.colimit_eq_iff (F := D₂)).mp hxy
  rw [← η.naturality_apply f a₁, ← η.naturality_apply g a₂] at heq
  exact (CategoryTheory.Limits.colimit_eq_iff (F := D₁)).mpr ⟨k, f, g, hη k heq⟩

/-! ### Helpers for Statement 5 -/

/-- Joint surjectivity of plus colimit coprojections. -/
@[sga "3 IV 4.3.10", sga "4 II 3.1"]
lemma plus_exists_meq_rep
    (F : Cᵒᵖ ⥤ Type u) (U : C) (s : (J.plusObj F).obj (op U)) :
    ∃ (𝒰 : J.Cover U) (mq : Meq F 𝒰),
      (Plus.mk mq : (J.plusObj F).obj (op U)) = s := by
  obtain ⟨j, x, hx⟩ :=
    Limits.Types.jointly_surjective (J.diagram F U) (Limits.colimit.isColimit _) s
  change Limits.multiequalizer (j.unop.index F) at x
  refine ⟨j.unop, (Meq.equiv F j.unop) x, ?_⟩
  change Limits.colimit.ι (J.diagram F U) (op j.unop)
      ((Meq.equiv F j.unop).symm ((Meq.equiv F j.unop) x)) = s
  rw [Equiv.symm_apply_apply]
  exact hx

/-- `Meq` compatibility under restriction along a refinement arrow. -/
lemma meq_restriction
    {F : Cᵒᵖ ⥤ Type u} {U : C} (𝒰 : J.Cover U) (mq : Meq F 𝒰)
    {V W : C} (f : V ⟶ U) (hf : 𝒰.1 f) (g : W ⟶ V) :
    F.map g.op (mq ⟨V, f, hf⟩) =
      mq ⟨W, g ≫ f, 𝒰.1.downward_closed hf g⟩ := by
  let I₁ : 𝒰.Arrow := ⟨V, f, hf⟩
  let I₂ : 𝒰.Arrow := ⟨W, g ≫ f, 𝒰.1.downward_closed hf g⟩
  let ar : I₁.Relation I₂ :=
    { Z := W, g₁ := g, g₂ := 𝟙 W, w := by simp [I₁, I₂] }
  let r : 𝒰.Relation := Cover.Relation.mk ar
  simpa [r, ar, I₁, I₂, Cover.shape, CategoryTheory.id_apply] using mq.condition r

/-- Explicit description of `toPlus` on a section as a `Plus.mk` over the top cover. -/
@[sga "4 II 3.0.5" "(X)"]
lemma toPlus_app_eq_mk (F : Cᵒᵖ ⥤ Type u) (V : C) (x : F.obj (op V)) :
    (J.toPlus F).app (op V) x =
      Plus.mk (Meq.mk (X := V) (P := F) ⊤ x) :=
  GrothendieckTopology.Plus.toPlus_eq_mk (J := J) (P := F) x

/-- Restriction of `Plus.mk` along a morphism is `Plus.mk` of the pullback. -/
@[sga "4 II 3.0.5" "special case"]
lemma plusObj_map_mk_pullback {F : Cᵒᵖ ⥤ Type u} {U : C}
    (𝒰 : J.Cover U) (mq : Meq F 𝒰) {V : C} (f : V ⟶ U) :
    (J.plusObj F).map f.op (Plus.mk mq) = Plus.mk (mq.pullback f) :=
  Plus.res_mk_eq_mk_pullback mq f

/-- Class equality on common refinement. -/
@[sga "4 II 3.1"]
lemma mk_top_eq_mk_pullback (F : Cᵒᵖ ⥤ Type u) {U : C} (𝒰 : J.Cover U)
    (mq : Meq F 𝒰) {V : C} (f : V ⟶ U) (hf : 𝒰.1 f) :
    Plus.mk (Meq.mk (X := V) (P := F) ⊤ (mq ⟨V, f, hf⟩)) =
      Plus.mk (mq.pullback f) := by
  rw [Plus.eq_mk_iff_exists]
  refine ⟨(J.pullback f).obj 𝒰, homOfLE le_top, 𝟙 _, ?_⟩
  ext I
  exact meq_restriction J 𝒰 mq f hf I.f

/-- Image of `(J.toPlus F).app` on a section indexed by an arrow of `𝒰` is
the pullback of `Plus.mk mq`. -/
@[sga "3 IV 4.3.10", sga "4 II 3.1"]
lemma toPlus_app_mq_arrow
    (F : Cᵒᵖ ⥤ Type u) {U : C} (𝒰 : J.Cover U) (mq : Meq F 𝒰)
    {V : C} (f : V ⟶ U) (hf : 𝒰.1 f) :
    (J.toPlus F).app (op V) (mq ⟨V, f, hf⟩) =
      (J.plusObj F).map f.op (Plus.mk mq) := by
  rw [toPlus_app_eq_mk J F V (mq ⟨V, f, hf⟩),
      mk_top_eq_mk_pullback J F 𝒰 mq f hf,
      ← plusObj_map_mk_pullback J 𝒰 mq f]

/-- A compatible family produces a sieve natural transformation realising the `Plus.mk` class. -/
lemma exists_sieveNatTrans_of_meq
    (F : Cᵒᵖ ⥤ Type u) {U : C} (𝒰 : J.Cover U) (mq : Meq F 𝒰) :
    ∃ φ : 𝒰.1.functor ⟶ F,
      φ ≫ J.toPlus F =
        𝒰.1.functorInclusion ≫
          (CategoryTheory.yonedaEquiv.symm
            (Plus.mk mq : (J.plusObj F).obj (op U))) := by
  refine ⟨{ app := fun V => ↾fun (f : 𝒰.1.functor.obj V) => mq ⟨V.unop, f.1, f.2⟩
            naturality := ?_ }, ?_⟩
  · intro V W g
    ext ⟨f, hf⟩
    exact (meq_restriction J 𝒰 mq f hf g.unop).symm
  · ext V ⟨f, hf⟩
    -- `(yonedaEquiv.symm x).app V f` is by definition `(J.plusObj F).map f.op x`; state the
    -- goal in that form directly rather than rewriting with `yonedaEquiv_symm_app_apply`,
    -- whose left-hand side is now stated up to `dsimp%`.
    change (J.toPlus F).app V (mq ⟨V.unop, f, hf⟩) =
         (J.plusObj F).map f.op (Plus.mk mq : (J.plusObj F).obj (op U))
    exact toPlus_app_mq_arrow J F 𝒰 mq f hf

/-! ### Main statements -/

/-- **Stacks 00ZH (1)**, identity law: restriction in `F⁺` along an identity arrow is the
identity, one half of `F⁺` being a presheaf. -/
@[stacks 00ZH "(1)", sga "4 II 3.0.5" "LF presheaf: id law"]
theorem statement1_map_id (F : Cᵒᵖ ⥤ Type u) (U : Cᵒᵖ) :
    (J.plusObj F).map (𝟙 U) = 𝟙 ((J.plusObj F).obj U) :=
  (J.plusObj F).map_id U

/-- **Stacks 00ZH (1)**, composition law: restricting in `F⁺` along `f ≫ g` is restricting
along `f` and then along `g`, the other half of `F⁺` being a presheaf. -/
@[stacks 00ZH "(1)", sga "4 II 3.0.5" "LF presheaf: comp law"]
theorem statement1_map_comp (F : Cᵒᵖ ⥤ Type u)
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    (J.plusObj F).map (f ≫ g) = (J.plusObj F).map f ≫ (J.plusObj F).map g :=
  (J.plusObj F).map_comp f g

/-- **Stacks 00ZH (2)**: `ℓ : F ⟶ F⁺` is a morphism of presheaves, i.e. its components commute
with restriction along any arrow `f`. -/
@[stacks 00ZH "(2)", sga "4 II 3.0.5" "ℓ(F):F→LF is natural"]
theorem statement2_ell_natural (F : Cᵒᵖ ⥤ Type u) {U V : Cᵒᵖ} (f : U ⟶ V) :
    F.map f ≫ (J.toPlus F).app V = (J.toPlus F).app U ≫ (J.plusObj F).map f :=
  (J.toPlus F).naturality f

/-- **Stacks 00ZH (3)**, identity law for `F ↦ F⁺` as an operation on presheaves:
`(𝟙 F)⁺ = 𝟙 F⁺`. -/
@[stacks 00ZH "(3)"]
theorem statement3a_map_id (F : Cᵒᵖ ⥤ Type u) :
    (J.plusFunctor (Type u)).map (𝟙 F) = 𝟙 ((J.plusFunctor (Type u)).obj F) :=
  (J.plusFunctor (Type u)).map_id F

/-- **Stacks 00ZH (3)**, composition law for `F ↦ F⁺` as an operation on presheaves:
`(α ≫ β)⁺ = α⁺ ≫ β⁺`. -/
@[stacks 00ZH "(3)"]
theorem statement3a_map_comp {F G H : Cᵒᵖ ⥤ Type u} (α : F ⟶ G) (β : G ⟶ H) :
    (J.plusFunctor (Type u)).map (α ≫ β) =
      (J.plusFunctor (Type u)).map α ≫ (J.plusFunctor (Type u)).map β :=
  (J.plusFunctor (Type u)).map_comp α β

/-- **Stacks 00ZH (3)**, naturality of `ℓ` in the presheaf variable: the square
`α ≫ ℓ G = ℓ F ≫ α⁺` commutes, so `ℓ` is a natural transformation `𝟭 ⟶ plusFunctor`. -/
@[stacks 00ZH "(3)"]
theorem statement3b_ell_natural {F G : Cᵒᵖ ⥤ Type u} (α : F ⟶ G) :
    α ≫ J.toPlus G = J.toPlus F ≫ J.plusMap α :=
  J.toPlus_naturality α

/-- **Stacks 00ZH (4)**: if `α : F ⟶ G` is injective on sections over every object, then so is
`α⁺`. The sections of `F⁺` over `U` form a filtered colimit of multiequalizers, and
injectivity survives both `diagramNatTrans` and the filtered colimit. -/
@[stacks 00ZH "(4)", sga "3 IV 4.3.10.0"]
theorem statement4_preserves_mono
    {F G : Cᵒᵖ ⥤ Type u} (α : F ⟶ G)
    (hα : ∀ U : Cᵒᵖ, Function.Injective (α.app U)) :
    ∀ U : Cᵒᵖ, Function.Injective ((J.plusMap α).app U) := by
  intro U
  obtain ⟨U₀, rfl⟩ : ∃ U₀ : C, op U₀ = U := ⟨U.unop, rfl⟩
  exact filtered_colim_inj_of_componentwise_inj _
    (diagram_map_injective_of_app_injective J α hα U₀)

/-- **Stacks 00ZH (5)**: every section `s` of `F⁺` over `U` is locally in the image of `ℓ` —
there is a covering sieve `S ∈ J U` and a `φ : S.functor ⟶ F` with `φ ≫ J.toPlus F` equal to the
restriction of `s` to `S`, expressed via `S.functorInclusion` and `yonedaEquiv.symm s`. -/
@[stacks 00ZH "(5)"]
theorem statement5_local_representability
    (F : Cᵒᵖ ⥤ Type u) (U : C) (s : (J.plusObj F).obj (op U)) :
    ∃ (S : Sieve U) (_ : S ∈ J U) (φ : S.functor ⟶ F),
      φ ≫ J.toPlus F =
        S.functorInclusion ≫ (CategoryTheory.yonedaEquiv.symm s) := by
  obtain ⟨𝒰, mq, hmq⟩ := plus_exists_meq_rep J F U s
  obtain ⟨φ, hφ⟩ := exists_sieveNatTrans_of_meq J F 𝒰 mq
  refine ⟨𝒰.1, 𝒰.2, φ, ?_⟩
  rw [hφ]
  subst hmq
  rfl

