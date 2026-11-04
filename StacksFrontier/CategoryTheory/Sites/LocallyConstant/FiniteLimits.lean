module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.CategoryTheory.Sites.Sheafification.LocalRepresentatives
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import Mathlib.CategoryTheory.FinCategory.AsType
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Coequalizers
import StacksCore.Tactic.StacksAttribute

/-!
# Finite locally constant sheaves of sets are closed under finite limits and colimits

Let `(C, J)` be a site. Stacks Tag 093U (1) asserts that the finite locally constant sheaves of
sets form a subcategory of `Sh(C)` closed under finite limits and finite colimits. This file
proves that.

## Main results

* `Stacks.ConstantSheaf.isFiniteLocallyConstantSetSheaf`: the property of objects of `Sh(C)`
  that the tag is about.
* **Tag 093U (1)** itself, carried by
  `isClosedUnderFiniteLimits_and_finiteColimits_isFiniteLocallyConstantSetSheaf`, together with
  the two closure instances it packages.
* `Stacks.ConstantSheaf.constantMapSieve_mem`: the constant case of Tag 093S (1), the engine.

## Implementation notes

The set universe is `Type (max u v w)` for a free `w`, exactly as the module universe of Tag
093U (3) is `ModuleCat.{max u v w}`. The reason is the same: the trivializing isomorphism
`mapPullbackConstantSheafIso`, which compares the constant sheaf on a slice site with the
restriction of the constant sheaf from a larger slice, needs
`(Over.map f).op.HasPointwiseRightKanExtension`, whose index categories live in
`Type (max u v)`. At a free set universe that fails; at `max u v w` every sheafification and Kan
extension hypothesis is automatic, and the universe is stable under slicing, since `Over U` has
objects in `Type (max u v)` and morphisms in `Type v`, so the recipe applied to `C/U` returns
`max (max u v) v w = max u v w`.

The argument never lifts a whole finite diagram to a diagram of finite sets. That route would
need the lifted maps of sets to be functorial, which requires the constant sheaf functor on the
slice site to be faithful; faithfulness fails over an object covered by the empty sieve, so the
route forces a degenerate case split, and it also needs one choice of local trivializations
compatible with every morphism of the shape at once. Instead the two generating shapes are
treated separately:

* for a finite *discrete* shape no morphism has to be trivialized at all, so a common refinement
  of the finitely many trivializing covers suffices;
* for a *parallel pair* the two morphisms are trivialized simultaneously by intersecting two
  copies of the sieve produced by `constantMapSieve_mem`.

Neither shape imposes a functoriality obligation, so no faithfulness is used anywhere, and the
general finite shape is reached through Mathlib's
`CategoryTheory.Limits.limitConeOfEqualizerAndProduct`, which exhibits a finite limit as an
equalizer of a map between two finite products.

`constantMapSieve_mem` is the constant-source, constant-target case of Tag 093S for sheaves of
sets: a map of constant sheaves whose source is a finite set is, on a covering of any object,
the constant map attached to an actual map of sets. It is the set-valued analogue of
`Stacks.ConstantSheaf.exists_cover_app_eq_constantSheaf_map`, and like that result it states its
conclusion sectionwise, over every object lying over a member of the covering, which is what
keeps the set universe free of further constraints.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ConstantSheaf

universe v u w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Recorded so that the searches below do not rediscover it. Sheafification of set-valued
presheaves exists in any universe containing the site; finding that out is the expensive step of
every instance search in this file, so it is done once. -/
private instance hasSheafify_typeMax : HasSheafify J (Type (max u v w)) := inferInstance

/-- Recorded so that the finite discrete shapes used below are found directly rather than by an
unbounded typeclass search through `HasWeakSheafify`. It is Mathlib's instance for sheaves,
specialized to the set universe of this file. -/
@[sga "4 II 4.8" "partial"]
private instance hasFiniteProducts_sheafTypeMax :
    HasFiniteProducts (Sheaf J (Type (max u v w))) := inferInstance

/-- Equalizers, recorded directly. -/
private instance hasEqualizers_sheafTypeMax :
    HasEqualizers (Sheaf J (Type (max u v w))) := inferInstance

/-- Coequalizers, recorded directly. -/
private instance hasCoequalizers_sheafTypeMax :
    HasCoequalizers (Sheaf J (Type (max u v w))) := inferInstance

/-- The coproduct counterpart of `hasFiniteProducts_sheafTypeMax`. -/
private instance hasFiniteCoproducts_sheafTypeMax :
    HasFiniteCoproducts (Sheaf J (Type (max u v w))) := inferInstance

/-- The finite discrete shape, recorded directly. -/
private instance hasLimitsOfShapeDiscrete_sheafTypeMax (ι : Type) [Finite ι] :
    HasLimitsOfShape (Discrete ι) (Sheaf J (Type (max u v w))) :=
  Limits.hasLimitsOfShape_discrete _ ι

/-- The finite discrete shape, recorded directly, for colimits. -/
private instance hasColimitsOfShapeDiscrete_sheafTypeMax (ι : Type) [Finite ι] :
    HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v w))) :=
  Limits.hasColimitsOfShape_discrete _ ι

/-- The finite coproduct itself, recorded directly: the generic step from
`HasColimitsOfShape` to `HasColimit` is not found within the search budget here. -/
@[sga "4 II 4.8" "special case"]
private instance (priority := 10000) hasColimitDiscreteFunctor_sheafTypeMax {ι : Type} [Finite ι]
    (F : ι → Sheaf J (Type (max u v w))) : HasColimit (Discrete.functor F) :=
  Limits.HasColimitsOfShape.has_colimit _

/-- The finite product itself, recorded directly. -/
private instance (priority := 10000) hasLimitDiscreteFunctor_sheafTypeMax {ι : Type} [Finite ι]
    (F : ι → Sheaf J (Type (max u v w))) : HasLimit (Discrete.functor F) :=
  Limits.HasLimitsOfShape.has_limit _

/-! ### Local triviality as a sieve -/

/-- `F` becomes, after restriction to the slice site `C/V`, the constant sheaf attached to a
finite set. -/
def IsConstantFiniteOver (V : C) (F : Sheaf J (Type (max u v w))) : Prop :=
  ∃ E : Type (max u v w), Finite E ∧
    Nonempty ((constantSheaf (J.over V) (Type (max u v w))).obj E ≅
      (J.overPullback (Type (max u v w)) V).obj F)

/-- Local triviality with finite value passes to objects lying over a given one. -/
theorem IsConstantFiniteOver.restrict {U V : C} (g : V ⟶ U)
    {F : Sheaf J (Type (max u v w))} (h : IsConstantFiniteOver.{v, u, w} J U F) :
    IsConstantFiniteOver.{v, u, w} J V F := by
  obtain ⟨E, hE, ⟨φ⟩⟩ := h
  exact ⟨E, hE, ⟨(mapPullbackConstantSheafIso J (Type (max u v w)) g).app E ≪≫
    (J.overMapPullback (Type (max u v w)) g).mapIso φ⟩⟩

/-- The arrows over which `F` becomes constant with finite value. This is a sieve because the
condition names only the source of the arrow. -/
def finTrivSieve (F : Sheaf J (Type (max u v w))) (U : C) : Sieve U where
  arrows V _ := IsConstantFiniteOver.{v, u, w} J V F
  downward_closed h g := h.restrict J g

/-- An arrow `g : V ⟶ U` lies in `finTrivSieve J F U` exactly when `F` is constant with finite
value over `V`. -/
@[simp]
theorem mem_finTrivSieve_iff {F : Sheaf J (Type (max u v w))} {U V : C} (g : V ⟶ U) :
    (finTrivSieve.{v, u, w} J F U) g ↔ IsConstantFiniteOver.{v, u, w} J V F :=
  Iff.rfl

/-- Being finite locally constant is exactly: the trivializing sieve covers every object. -/
theorem isFiniteLocallyConstant_iff_trivSieve_mem (F : Sheaf J (Type (max u v w))) :
    IsFiniteLocallyConstant J F ↔ ∀ U : C, finTrivSieve.{v, u, w} J F U ∈ J U := by
  constructor
  · intro hF U
    obtain ⟨I, X, f, hf, h⟩ := hF.exists_finite_cover U
    refine J.superset_covering ?_ hf
    rw [Sieve.generate_le_iff]
    rintro Y p ⟨i⟩
    exact h i
  · intro hF
    refine ⟨fun U ↦ ?_⟩
    obtain ⟨I, X, f, hXf⟩ := Sieve.exists_eq_ofArrows (finTrivSieve.{v, u, w} J F U)
    refine ⟨I, X, f, hXf ▸ hF U, fun i ↦ ?_⟩
    have : (finTrivSieve.{v, u, w} J F U) (f i) := by
      rw [hXf]
      exact Sieve.ofArrows_mk X f i
    exact this

/-- Local triviality is itself local: if a covering sieve consists of arrows over whose sources
the trivializing sieve covers, then it covers. -/
theorem finTrivSieve_mem_of_cover {F : Sheaf J (Type (max u v w))} {U : C} {S : Sieve U}
    (hS : S ∈ J U)
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ U), S g → finTrivSieve.{v, u, w} J F Y ∈ J Y) :
    finTrivSieve.{v, u, w} J F U ∈ J U :=
  J.transitive hS _ (fun _ g hg ↦ h g hg)

/-! ### A map of constant sheaves of sets is locally a constant map -/

section ConstantMaps

/-- The canonical map from a set to the sections of its constant sheaf is compatible with
restriction: the constant presheaf has identity restriction maps, so the image of an element
restricts to the image of the same element. -/
theorem map_constantUnit_type (A : Type (max u v w)) {X Y : Cᵒᵖ} (p : X ⟶ Y) (a : A) :
    (sheafify J ((Functor.const Cᵒᵖ).obj A)).map p
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app X a) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app Y a :=
  (NatTrans.naturality_apply (toSheafify J ((Functor.const Cᵒᵖ).obj A)) p a).symm

/-- The constant map attached to `g : A ⟶ B` takes the canonical image of `a` to the canonical
image of `g a`, with the sections spelled through `sheafify`. -/
theorem constantUnit_map_constantSheaf {A B : Type (max u v w)} (g : A ⟶ B) (X : Cᵒᵖ) (a : A) :
    (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app X (g a) =
      ((constantSheaf J (Type (max u v w))).map g).hom.app X
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app X a) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality J ((Functor.const Cᵒᵖ).map g)) X) a
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply] at h
  exact h

/-- Two morphisms out of a constant sheaf of sets which agree on the canonical image of the set
over every object lying over `V` agree on every section over every such object.

Every section of `A̲` is locally the canonical image of an element of `A`, because `toSheafify` is
locally surjective, and the target is a sheaf, hence separated. -/
theorem apply_eq_of_eq_on_constantUnit_type {A : Type (max u v w)}
    {G : Sheaf J (Type (max u v w))}
    (ξ ξ' : (constantSheaf J (Type (max u v w))).obj A ⟶ G) {V : C}
    (h : ∀ (W : C) (_ : W ⟶ V) (a : A),
      ξ.hom.app (op W) ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op W) a) =
        ξ'.hom.app (op W) ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op W) a))
    (W : C) (p : W ⟶ V)
    (t : ((constantSheaf J (Type (max u v w))).obj A).obj.obj (op W)) :
    ξ.hom.app (op W) t = ξ'.hom.app (op W) t := by
  have hls : Presheaf.IsLocallySurjective J
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)) :=
    Stacks.Sheafification.isLocallySurjective_toSheafify_type J _
  refine G.property.isSeparated _ _ (Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)) t) _ _ ?_
  rintro Y q ⟨a, ha⟩
  have ha' : (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op Y) a =
      ((constantSheaf J (Type (max u v w))).obj A).obj.map q.op t := ha
  calc G.obj.map q.op (ξ.hom.app (op W) t)
      = ξ.hom.app (op Y)
          (((constantSheaf J (Type (max u v w))).obj A).obj.map q.op t) :=
        (NatTrans.naturality_apply ξ.hom q.op t).symm
    _ = ξ.hom.app (op Y) ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op Y) a) := by
        rw [ha']
    _ = ξ'.hom.app (op Y) ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op Y) a) :=
        h Y (q ≫ p) a
    _ = ξ'.hom.app (op Y)
          (((constantSheaf J (Type (max u v w))).obj A).obj.map q.op t) := by rw [ha']
    _ = G.obj.map q.op (ξ'.hom.app (op W) t) :=
        NatTrans.naturality_apply ξ'.hom q.op t

/-- The morphism form of `Stacks.ConstantSheaf.apply_eq_of_eq_on_constantUnit_type`. -/
theorem app_eq_of_eq_on_constantUnit_type {A : Type (max u v w)}
    {G : Sheaf J (Type (max u v w))}
    (ξ ξ' : (constantSheaf J (Type (max u v w))).obj A ⟶ G) {V : C}
    (h : ∀ (W : C) (_ : W ⟶ V) (a : A),
      ξ.hom.app (op W) ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op W) a) =
        ξ'.hom.app (op W) ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op W) a))
    (W : C) (p : W ⟶ V) : ξ.hom.app (op W) = ξ'.hom.app (op W) := by
  ext t
  exact apply_eq_of_eq_on_constantUnit_type J ξ ξ' h W p t

/-- The arrows over whose source a map of constant sheaves of sets is the constant map attached
to an actual map of sets. This is a sieve because the condition names only the source. -/
def constantMapSieve {A B : Type (max u v w)}
    (ξ : (constantSheaf J (Type (max u v w))).obj A ⟶
      (constantSheaf J (Type (max u v w))).obj B) (U : C) : Sieve U where
  arrows V _ := ∃ g : A ⟶ B, ∀ (W : C) (_ : W ⟶ V),
    ξ.hom.app (op W) = ((constantSheaf J (Type (max u v w))).map g).hom.app (op W)
  downward_closed := by
    rintro V V' r ⟨g, hg⟩ q
    exact ⟨g, fun W p ↦ hg W (p ≫ q)⟩

/-- **A map of constant sheaves of sets is locally a constant map.** If `A` is finite then the
arrows over whose source `ξ` agrees with the constant map attached to some map of sets `A ⟶ B`
form a covering sieve of every object.

This is the constant-source, constant-target case of Stacks Tag 093S (1). The proof: `ξ`
determines the family of sections `ξ(a)` of `B̲` indexed by `A`; since `A` is finite and the
canonical map `B → Γ(-, B̲)` is locally surjective, these have simultaneous representatives in
`B` on a covering family; and over a member of that family the two morphisms agree on the
canonical image of `A`, hence agree, because `B̲` is separated. -/
@[sga "4 IX 2.1" "(i), special case"]
theorem constantMapSieve_mem {A B : Type (max u v w)} [Finite A]
    (ξ : (constantSheaf J (Type (max u v w))).obj A ⟶
      (constantSheaf J (Type (max u v w))).obj B) (U : C) :
    constantMapSieve.{v, u, w} J ξ U ∈ J U := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin A
  obtain ⟨I, V, f, hf, hV⟩ := Stacks.Sheafification.exists_cover_constant_representatives J B U
    (fun k : Fin n ↦ ξ.hom.app (op U)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op U) (e.symm k)))
  refine J.superset_covering ?_ hf
  rw [Sieve.generate_le_iff]
  rintro Y p ⟨i⟩
  choose b hb using (hV i).2
  refine ⟨TypeCat.ofHom (fun a ↦ b (e a)), fun W q ↦ ?_⟩
  refine app_eq_of_eq_on_constantUnit_type J ξ _ (V := V i) (fun W' q' a ↦ ?_) W q
  have hb' : (sheafify J ((Functor.const Cᵒᵖ).obj B)).map (f i).op
      (ξ.hom.app (op U) ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op U) a)) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op (V i)) (b (e a)) := by
    simpa only [Equiv.symm_apply_apply] using hb (e a)
  -- the statement over `V i`
  have key : ξ.hom.app (op (V i))
      ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op (V i)) a) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op (V i)) (b (e a)) := by
    have h1 : ξ.hom.app (op (V i))
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op (V i)) a) =
        ξ.hom.app (op (V i)) ((sheafify J ((Functor.const Cᵒᵖ).obj A)).map (f i).op
          ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op U) a)) := by
      rw [map_constantUnit_type J A (f i).op a]
    exact h1.trans ((NatTrans.naturality_apply ξ.hom ((f i).op) _).trans hb')
  -- restrict it along `q' : W' ⟶ V i`
  have h4 : ξ.hom.app (op W')
      ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op W') a) =
      ξ.hom.app (op W') ((sheafify J ((Functor.const Cᵒᵖ).obj A)).map q'.op
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op (V i)) a)) := by
    rw [map_constantUnit_type J A q'.op a]
  have h5 : (sheafify J ((Functor.const Cᵒᵖ).obj B)).map q'.op
      (ξ.hom.app (op (V i))
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op (V i)) a)) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op W') (b (e a)) := by
    rw [key]
    exact map_constantUnit_type J B q'.op (b (e a))
  exact h4.trans (((NatTrans.naturality_apply ξ.hom q'.op _).trans h5).trans
    (constantUnit_map_constantSheaf J (TypeCat.ofHom (fun a ↦ b (e a))) (op W') a))

end ConstantMaps

/-! ### Exactness of the two functors involved -/

section Exactness

/-- The constant sheaf functor on a slice site preserves finite limits: it is the constant
presheaf functor, which preserves all limits, followed by sheafification, which is left
exact. -/
instance preservesFiniteLimits_constantSheaf_over_type (V : C) :
    PreservesFiniteLimits (constantSheaf (J.over V) (Type (max u v w))) := by
  dsimp only [constantSheaf]
  exact comp_preservesFiniteLimits _ _

/-- The constant sheaf functor on a slice site preserves finite colimits: it is a left adjoint,
the right adjoint being evaluation at the terminal object `𝟙 V` of `C/V`. -/
instance preservesFiniteColimits_constantSheaf_over_type (V : C) :
    PreservesFiniteColimits (constantSheaf (J.over V) (Type (max u v w))) := by
  have : PreservesColimitsOfSize.{0, 0} (constantSheaf (J.over V) (Type (max u v w))) :=
    (constantSheafAdj (J.over V) (Type (max u v w))
      (Over.mkIdTerminal (X := V))).leftAdjoint_preservesColimits
  infer_instance

end Exactness

/-! ### Transporting a local trivialization through a finite limit or colimit -/

section Transport

/-- If a finite diagram of sheaves becomes, after restriction to `C/Z`, the diagram of constant
sheaves attached to a finite diagram of sets, then its limit becomes the constant sheaf attached
to the limit of sets. Both functors preserve finite limits, so this is a composite of three
isomorphisms. -/
theorem isConstantFiniteOver_limit {K : Type} [SmallCategory K] [FinCategory K]
    {D₁ : K ⥤ Type (max u v w)} {D₂ : K ⥤ Sheaf J (Type (max u v w))} (Z : C)
    [Finite (limit D₁)]
    (e : D₁ ⋙ constantSheaf (J.over Z) (Type (max u v w)) ≅
      D₂ ⋙ J.overPullback (Type (max u v w)) Z) :
    IsConstantFiniteOver.{v, u, w} J Z (limit D₂) :=
  ⟨limit D₁, inferInstance,
    ⟨preservesLimitIso (constantSheaf (J.over Z) (Type (max u v w))) D₁ ≪≫
      HasLimit.isoOfNatIso e ≪≫
      (preservesLimitIso (J.overPullback (Type (max u v w)) Z) D₂).symm⟩⟩

/-- The colimit counterpart of `Stacks.ConstantSheaf.isConstantFiniteOver_limit`. -/
theorem isConstantFiniteOver_colimit {K : Type} [SmallCategory K] [FinCategory K]
    {D₁ : K ⥤ Type (max u v w)} {D₂ : K ⥤ Sheaf J (Type (max u v w))} (Z : C)
    [Finite (colimit D₁)]
    (e : D₁ ⋙ constantSheaf (J.over Z) (Type (max u v w)) ≅
      D₂ ⋙ J.overPullback (Type (max u v w)) Z) :
    IsConstantFiniteOver.{v, u, w} J Z (colimit D₂) :=
  ⟨colimit D₁, inferInstance,
    ⟨preservesColimitIso (constantSheaf (J.over Z) (Type (max u v w))) D₁ ≪≫
      HasColimit.isoOfNatIso e ≪≫
      (preservesColimitIso (J.overPullback (Type (max u v w)) Z) D₂).symm⟩⟩

end Transport

/-! ### Finite products and coproducts -/

section Products

/-- A finite product of sheaves that are constant with finite value over `Z` is constant with
finite value over `Z`. No morphism has to be trivialized, the shape being discrete. -/
theorem IsConstantFiniteOver.pi {ι : Type} [Finite ι] {Z : C}
    {F : ι → Sheaf J (Type (max u v w))} [HasProduct F]
    (h : ∀ i, IsConstantFiniteOver.{v, u, w} J Z (F i)) :
    IsConstantFiniteOver.{v, u, w} J Z (∏ᶜ F) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose E hE hα using h
  have hfin : Finite (limit (Discrete.functor E)) :=
    Finite.of_equiv _ (Types.productIso E).toEquiv.symm
  exact isConstantFiniteOver_limit J Z (D₁ := Discrete.functor E) (D₂ := Discrete.functor F)
    (Discrete.natIso (fun i ↦ (hα i.as).some))

/-- A finite coproduct of sheaves that are constant with finite value over `Z` is constant with
finite value over `Z`. -/
theorem IsConstantFiniteOver.sigma {ι : Type} [Finite ι] {Z : C}
    {F : ι → Sheaf J (Type (max u v w))} [HasCoproduct F]
    (h : ∀ i, IsConstantFiniteOver.{v, u, w} J Z (F i)) :
    IsConstantFiniteOver.{v, u, w} J Z (∐ F) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose E hE hα using h
  have hfin : Finite (colimit (Discrete.functor E)) :=
    Finite.of_equiv _ (Types.coproductIso E).toEquiv.symm
  exact isConstantFiniteOver_colimit J Z (D₁ := Discrete.functor E) (D₂ := Discrete.functor F)
    (Discrete.natIso (fun i ↦ (hα i.as).some))

/-- A sheaf is finite locally constant as soon as it is constant with finite value over every
object where all members of a finite family of finite locally constant sheaves are. -/
private theorem isFiniteLocallyConstant_of_forall {ι : Type} [Finite ι]
    (F : ι → Sheaf J (Type (max u v w))) (G : Sheaf J (Type (max u v w)))
    (h : ∀ i, IsFiniteLocallyConstant J (F i))
    (hG : ∀ {Z : C}, (∀ i, IsConstantFiniteOver.{v, u, w} J Z (F i)) →
      IsConstantFiniteOver.{v, u, w} J Z G) :
    IsFiniteLocallyConstant J G := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [isFiniteLocallyConstant_iff_trivSieve_mem]
  intro U
  have hcov : (Finset.univ.inf fun i ↦ finTrivSieve.{v, u, w} J (F i) U) ∈ J U :=
    Stacks.Sheafification.finsetInf_covering J Finset.univ _
      (fun i ↦ ((isFiniteLocallyConstant_iff_trivSieve_mem J (F i)).mp (h i)) U)
  refine J.superset_covering (fun Y p hp ↦ hG fun i ↦ ?_) hcov
  exact (Finset.inf_le (Finset.mem_univ i) : _ ≤ finTrivSieve.{v, u, w} J (F i) U) p hp

/-- A finite product of finite locally constant sheaves of sets is finite locally constant: the
finitely many trivializing sieves are intersected. -/
theorem isFiniteLocallyConstant_pi {ι : Type} [Finite ι]
    (F : ι → Sheaf J (Type (max u v w))) [HasProduct F]
    (h : ∀ i, IsFiniteLocallyConstant J (F i)) :
    IsFiniteLocallyConstant J (∏ᶜ F) :=
  isFiniteLocallyConstant_of_forall J F _ h (IsConstantFiniteOver.pi J)

/-- A finite coproduct of finite locally constant sheaves of sets is finite locally constant. -/
theorem isFiniteLocallyConstant_sigma {ι : Type} [Finite ι]
    (F : ι → Sheaf J (Type (max u v w))) [HasCoproduct F]
    (h : ∀ i, IsFiniteLocallyConstant J (F i)) :
    IsFiniteLocallyConstant J (∐ F) :=
  isFiniteLocallyConstant_of_forall J F _ h (IsConstantFiniteOver.sigma J)

end Products

/-! ### Pairs of parallel morphisms -/

section Pair

variable {F G : Sheaf J (Type (max u v w))}

/-- A trivialization of `F` over `U` restricted to an object `Z` lying over `U`. The result type
is ascribed so that the target is spelled `j_Z^{-1} F` rather than `j_q^{-1} j_U^{-1} F`; the two
are definitionally equal by `inverseImage_eq`. -/
noncomputable def restrictFinTrivIso {U Z : C} (q : Z ⟶ U) (E : Type (max u v w))
    (α : (constantSheaf (J.over U) (Type (max u v w))).obj E ≅
      (J.overPullback (Type (max u v w)) U).obj F) :
    (constantSheaf (J.over Z) (Type (max u v w))).obj E ≅
      (J.overPullback (Type (max u v w)) Z).obj F :=
  (mapPullbackConstantSheafApp J (Type (max u v w)) q E).trans
    ((J.overMapPullback (Type (max u v w)) q).mapIso α)

/-- The restricted square, stated entirely in the relocalization spelling `j_q^{-1}`, where it is
rewritable. -/
theorem restrictFinTriv_square {U Z : C} (q : Z ⟶ U) {f : F ⟶ G} {E E' : Type (max u v w)}
    (ψ : E ⟶ E')
    {α : (constantSheaf (J.over U) (Type (max u v w))).obj E ≅
      (J.overPullback (Type (max u v w)) U).obj F}
    {β : (constantSheaf (J.over U) (Type (max u v w))).obj E' ≅
      (J.overPullback (Type (max u v w)) U).obj G}
    (sq : (J.overMapPullback (Type (max u v w)) q).map
        (α.hom ≫ (J.overPullback (Type (max u v w)) U).map f) =
      (J.overMapPullback (Type (max u v w)) q).map
        ((constantSheaf (J.over U) (Type (max u v w))).map ψ ≫ β.hom)) :
    ((mapPullbackConstantSheafApp J (Type (max u v w)) q E).hom ≫
        (J.overMapPullback (Type (max u v w)) q).map α.hom) ≫
      (J.overMapPullback (Type (max u v w)) q).map
        ((J.overPullback (Type (max u v w)) U).map f) =
      (constantSheaf (J.over Z) (Type (max u v w))).map ψ ≫
        ((mapPullbackConstantSheafApp J (Type (max u v w)) q E').hom ≫
          (J.overMapPullback (Type (max u v w)) q).map β.hom) := by
  rw [Category.assoc, ← Functor.map_comp, sq, Functor.map_comp, ← Category.assoc,
    ← mapPullbackConstantSheafApp_naturality, Category.assoc]

/-- After restriction to the slice site `C/Z`, the pair `φ, ψ` is the pair of morphisms of
constant sheaves attached to a pair of maps of finite sets, with one trivialization of the source
and one of the target serving for both. -/
def IsConstantPairOver (Z : C) (φ ψ : F ⟶ G) : Prop :=
  ∃ (E E' : Type (max u v w)) (g h : E ⟶ E'), Finite E ∧ Finite E' ∧
    ∃ (α : (constantSheaf (J.over Z) (Type (max u v w))).obj E ≅
        (J.overPullback (Type (max u v w)) Z).obj F)
      (β : (constantSheaf (J.over Z) (Type (max u v w))).obj E' ≅
        (J.overPullback (Type (max u v w)) Z).obj G),
      α.hom ≫ (J.overPullback (Type (max u v w)) Z).map φ =
          (constantSheaf (J.over Z) (Type (max u v w))).map g ≫ β.hom ∧
        α.hom ≫ (J.overPullback (Type (max u v w)) Z).map ψ =
          (constantSheaf (J.over Z) (Type (max u v w))).map h ≫ β.hom

/-- If the pair `φ ψ : F ⟶ G` is constant over `Z`, then `F` is constant with finite value over
`Z`. -/
theorem IsConstantPairOver.source {Z : C} {φ ψ : F ⟶ G}
    (hp : IsConstantPairOver.{v, u, w} J Z φ ψ) : IsConstantFiniteOver.{v, u, w} J Z F := by
  obtain ⟨E, _, _, _, hE, _, α, _, _⟩ := hp
  exact ⟨E, hE, ⟨α⟩⟩

/-- If the pair `φ ψ : F ⟶ G` is constant over `Z`, then `G` is constant with finite value over
`Z`. -/
theorem IsConstantPairOver.target {Z : C} {φ ψ : F ⟶ G}
    (hp : IsConstantPairOver.{v, u, w} J Z φ ψ) : IsConstantFiniteOver.{v, u, w} J Z G := by
  obtain ⟨_, E', _, _, _, hE', _, β, _⟩ := hp
  exact ⟨E', hE', ⟨β⟩⟩

/-- The local description of a pair is inherited by every object lying over one where it holds:
restrict both squares along `Over.map q` and conjugate. -/
theorem IsConstantPairOver.restrict {U Z : C} (q : Z ⟶ U) {φ ψ : F ⟶ G}
    (hp : IsConstantPairOver.{v, u, w} J U φ ψ) :
    IsConstantPairOver.{v, u, w} J Z φ ψ := by
  obtain ⟨E, E', g, h, hE, hE', α, β, sqg, sqh⟩ := hp
  exact ⟨E, E', g, h, hE, hE', restrictFinTrivIso J q E α, restrictFinTrivIso J q E' β,
    restrictFinTriv_square J q g
      (congrArg (J.overMapPullback (Type (max u v w)) q).map sqg),
    restrictFinTriv_square J q h
      (congrArg (J.overMapPullback (Type (max u v w)) q).map sqh)⟩

/-- **The sieve on which a pair of parallel morphisms is constant.** -/
def constantPairSieve (φ ψ : F ⟶ G) (U : C) : Sieve U where
  arrows Z _ := IsConstantPairOver.{v, u, w} J Z φ ψ
  downward_closed hp g := hp.restrict J g

/-- If `F` and `G` both become constant with finite value after restriction to `C/Y₀`, then the
arrows on which both `φ` and `ψ` become morphisms of constant sheaves attached to maps of finite
sets, for one common pair of trivializations, cover `Y₀`.

The two trivializations turn the pair into a pair of endomaps of constant sheaves on the slice
site; `Stacks.ConstantSheaf.constantMapSieve_mem` applies to each, and the intersection of the
two resulting covering sieves is covering. -/
theorem constantPairSieve_mem (φ ψ : F ⟶ G) {Y₀ : C}
    (hF : IsConstantFiniteOver.{v, u, w} J Y₀ F)
    (hG : IsConstantFiniteOver.{v, u, w} J Y₀ G) :
    constantPairSieve.{v, u, w} J φ ψ Y₀ ∈ J Y₀ := by
  obtain ⟨E, hE, ⟨α₀⟩⟩ := hF
  obtain ⟨E', hE', ⟨β₀⟩⟩ := hG
  set ξ : (constantSheaf (J.over Y₀) (Type (max u v w))).obj E ⟶
      (constantSheaf (J.over Y₀) (Type (max u v w))).obj E' :=
    α₀.hom ≫ (J.overPullback (Type (max u v w)) Y₀).map φ ≫ β₀.inv with hξ
  set ζ : (constantSheaf (J.over Y₀) (Type (max u v w))).obj E ⟶
      (constantSheaf (J.over Y₀) (Type (max u v w))).obj E' :=
    α₀.hom ≫ (J.overPullback (Type (max u v w)) Y₀).map ψ ≫ β₀.inv with hζ
  set S : Sieve (Over.mk (𝟙 Y₀)) :=
    constantMapSieve (J.over Y₀) ξ (Over.mk (𝟙 Y₀)) ⊓
      constantMapSieve (J.over Y₀) ζ (Over.mk (𝟙 Y₀))
  have hS : S ∈ (J.over Y₀) (Over.mk (𝟙 Y₀)) :=
    (J.over Y₀).intersection_covering
      (constantMapSieve_mem (J.over Y₀) ξ (Over.mk (𝟙 Y₀)))
      (constantMapSieve_mem (J.over Y₀) ζ (Over.mk (𝟙 Y₀)))
  obtain ⟨I, V, g, hVg⟩ := Sieve.exists_eq_ofArrows S
  rw [hVg, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hS
  refine J.superset_covering ?_ hS
  rw [Sieve.generate_le_iff]
  rintro Z p ⟨i⟩
  have hmem : S (g i) := by
    rw [hVg]
    exact Sieve.ofArrows_mk V g i
  obtain ⟨gg, hgg⟩ := hmem.1
  obtain ⟨hh, hhh⟩ := hmem.2
  have hleft : (g i).left = (V i).hom := by simpa using Over.w (g i)
  have sq : ∀ (χ : F ⟶ G) (k : E ⟶ E'),
      (∀ (W : Over Y₀) (_ : W ⟶ V i),
        (α₀.hom ≫ (J.overPullback (Type (max u v w)) Y₀).map χ ≫ β₀.inv).hom.app (op W) =
          ((constantSheaf (J.over Y₀) (Type (max u v w))).map k).hom.app (op W)) →
      (restrictFinTrivIso J (V i).hom E α₀).hom ≫
          (J.overPullback (Type (max u v w)) (V i).left).map χ =
        (constantSheaf (J.over (V i).left) (Type (max u v w))).map k ≫
          (restrictFinTrivIso J (V i).hom E' β₀).hom := by
    intro χ k hk
    refine restrictFinTriv_square J (V i).hom k ?_
    have hres : (J.overMapPullback (Type (max u v w)) (V i).hom).map
        (α₀.hom ≫ (J.overPullback (Type (max u v w)) Y₀).map χ ≫ β₀.inv) =
        (J.overMapPullback (Type (max u v w)) (V i).hom).map
          ((constantSheaf (J.over Y₀) (Type (max u v w))).map k) :=
      Sheaf.hom_ext (NatTrans.ext (funext fun T ↦
        hk ((Over.map (V i).hom).obj T.unop) (Over.homMk T.unop.hom)))
    have h₁ : α₀.hom ≫ (J.overPullback (Type (max u v w)) Y₀).map χ =
        (α₀.hom ≫ (J.overPullback (Type (max u v w)) Y₀).map χ ≫ β₀.inv) ≫ β₀.hom := by
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h₁, Functor.map_comp, hres, ← Functor.map_comp]
  have key : IsConstantPairOver.{v, u, w} J (V i).left φ ψ :=
    ⟨E, E', gg, hh, hE, hE', restrictFinTrivIso J (V i).hom E α₀,
      restrictFinTrivIso J (V i).hom E' β₀, sq φ gg hgg, sq ψ hh hhh⟩
  exact hleft ▸ key

/-- An equalizer of a pair which is locally constant over `Z` is constant with finite value over
`Z`: the equalizer of the two maps of finite sets is a subtype of a finite set. -/
theorem IsConstantPairOver.equalizer {Z : C} {φ ψ : F ⟶ G}
    (hp : IsConstantPairOver.{v, u, w} J Z φ ψ) :
    IsConstantFiniteOver.{v, u, w} J Z (Limits.equalizer φ ψ) := by
  obtain ⟨E, E', g, h, hE, hE', α, β, sqg, sqh⟩ := hp
  have hfin : Finite (limit (parallelPair g h)) :=
    Finite.of_equiv _ (Types.equalizerIso g h).toEquiv.symm
  exact isConstantFiniteOver_limit J Z (D₁ := parallelPair g h) (D₂ := parallelPair φ ψ)
    (parallelPair.ext α β sqg.symm sqh.symm)

/-- A coequalizer of a pair which is locally constant over `Z` is constant with finite value over
`Z`: the coequalizer of the two maps of finite sets is a quotient of a finite set. -/
theorem IsConstantPairOver.coequalizer {Z : C} {φ ψ : F ⟶ G}
    (hp : IsConstantPairOver.{v, u, w} J Z φ ψ) :
    IsConstantFiniteOver.{v, u, w} J Z (Limits.coequalizer φ ψ) := by
  obtain ⟨E, E', g, h, hE, hE', α, β, sqg, sqh⟩ := hp
  have hcoeq : Finite (Function.Coequalizer
      (ConcreteCategory.hom g) (ConcreteCategory.hom h)) :=
    Finite.of_surjective _ (Function.Coequalizer.mk_surjective _ _)
  have hfin : Finite (colimit (parallelPair g h)) :=
    Finite.of_equiv _ (Types.coequalizerIso g h).toEquiv.symm
  exact isConstantFiniteOver_colimit J Z (D₁ := parallelPair g h) (D₂ := parallelPair φ ψ)
    (parallelPair.ext α β sqg.symm sqh.symm)

/-- The sieve on which a pair is constant covers every object, as soon as source and target are
finite locally constant. -/
theorem constantPairSieve_mem_of_isFiniteLocallyConstant (φ ψ : F ⟶ G)
    (hF : IsFiniteLocallyConstant J F) (hG : IsFiniteLocallyConstant J G) (U : C) :
    constantPairSieve.{v, u, w} J φ ψ U ∈ J U := by
  rw [isFiniteLocallyConstant_iff_trivSieve_mem] at hF hG
  exact J.transitive (J.intersection_covering (hF U) (hG U)) _
    fun _ _ hq ↦ constantPairSieve_mem J φ ψ hq.1 hq.2

/-- A sheaf which is constant with finite value over every object where a pair of morphisms
of finite locally constant sheaves is locally constant is finite locally constant. -/
private theorem isFiniteLocallyConstant_of_pair (φ ψ : F ⟶ G) (H : Sheaf J (Type (max u v w)))
    (hF : IsFiniteLocallyConstant J F) (hG : IsFiniteLocallyConstant J G)
    (hH : ∀ {Z : C}, IsConstantPairOver.{v, u, w} J Z φ ψ → IsConstantFiniteOver.{v, u, w} J Z H) :
    IsFiniteLocallyConstant J H := by
  rw [isFiniteLocallyConstant_iff_trivSieve_mem]
  intro U
  exact J.superset_covering (fun _ _ hq ↦ hH hq)
    (constantPairSieve_mem_of_isFiniteLocallyConstant J φ ψ hF hG U)

/-- An equalizer of two morphisms of finite locally constant sheaves of sets is finite locally
constant. -/
theorem isFiniteLocallyConstant_equalizer (φ ψ : F ⟶ G)
    (hF : IsFiniteLocallyConstant J F) (hG : IsFiniteLocallyConstant J G) :
    IsFiniteLocallyConstant J (Limits.equalizer φ ψ) :=
  isFiniteLocallyConstant_of_pair J φ ψ _ hF hG (IsConstantPairOver.equalizer J)

/-- A coequalizer of two morphisms of finite locally constant sheaves of sets is finite locally
constant. -/
theorem isFiniteLocallyConstant_coequalizer (φ ψ : F ⟶ G)
    (hF : IsFiniteLocallyConstant J F) (hG : IsFiniteLocallyConstant J G) :
    IsFiniteLocallyConstant J (Limits.coequalizer φ ψ) :=
  isFiniteLocallyConstant_of_pair J φ ψ _ hF hG (IsConstantPairOver.coequalizer J)

end Pair

/-! ### Tag 093U (1) -/

section Main

/-- Being a finite locally constant sheaf of sets, as a property of objects of `Sh(C)`. -/
def isFiniteLocallyConstantSetSheaf : ObjectProperty (Sheaf J (Type (max u v w))) :=
  fun F ↦ IsFiniteLocallyConstant J F

/-- The finite locally constant sheaves of sets are closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_isFiniteLocallyConstantSetSheaf :
    ObjectProperty.IsClosedUnderIsomorphisms
      (isFiniteLocallyConstantSetSheaf.{v, u, w} J) where
  of_iso {F F'} e hF := by
    refine ⟨fun U ↦ ?_⟩
    obtain ⟨I, V, f, hcov, h⟩ := hF.exists_finite_cover U
    refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
    obtain ⟨E, hE, ⟨φ⟩⟩ := h i
    exact ⟨E, hE, ⟨φ ≪≫ (J.overPullback (Type (max u v w)) (V i)).mapIso e⟩⟩

/-- A finite limit of finite locally constant sheaves of sets is finite locally constant. -/
theorem isFiniteLocallyConstant_limit {K : Type} [SmallCategory K] [FinCategory K]
    (D : K ⥤ Sheaf J (Type (max u v w))) [HasLimit D]
    (h : ∀ k, IsFiniteLocallyConstant J (D.obj k)) :
    IsFiniteLocallyConstant J (limit D) := by
  have hmor : Finite ((p : K × K) × (p.1 ⟶ p.2)) := inferInstance
  have hprod : IsFiniteLocallyConstant J (∏ᶜ D.obj) :=
    isFiniteLocallyConstant_pi J D.obj h
  have hprod' : IsFiniteLocallyConstant J (∏ᶜ fun f : (p : K × K) × (p.1 ⟶ p.2) ↦ D.obj f.1.2) :=
    isFiniteLocallyConstant_pi J _ (fun f ↦ h f.1.2)
  have hiso : limit D ≅ (limitConeOfEqualizerAndProduct D).cone.pt :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit D) (limitConeOfEqualizerAndProduct D).isLimit
  exact ObjectProperty.prop_of_iso (isFiniteLocallyConstantSetSheaf.{v, u, w} J) hiso.symm
    (isFiniteLocallyConstant_equalizer J _ _ hprod hprod')

/-- A finite colimit of finite locally constant sheaves of sets is finite locally constant. -/
theorem isFiniteLocallyConstant_colimit {K : Type} [SmallCategory K] [FinCategory K]
    (D : K ⥤ Sheaf J (Type (max u v w))) [HasColimit D]
    (h : ∀ k, IsFiniteLocallyConstant J (D.obj k)) :
    IsFiniteLocallyConstant J (colimit D) := by
  have hmor : Finite ((p : K × K) × (p.1 ⟶ p.2)) := inferInstance
  have hcop : IsFiniteLocallyConstant J (∐ D.obj) :=
    isFiniteLocallyConstant_sigma J D.obj h
  have hcop' : IsFiniteLocallyConstant J (∐ fun f : (p : K × K) × (p.1 ⟶ p.2) ↦ D.obj f.1.1) :=
    isFiniteLocallyConstant_sigma J _ (fun f ↦ h f.1.1)
  have hiso : colimit D ≅ (colimitCoconeOfCoequalizerAndCoproduct D).cocone.pt :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit D)
      (colimitCoconeOfCoequalizerAndCoproduct D).isColimit
  exact ObjectProperty.prop_of_iso (isFiniteLocallyConstantSetSheaf.{v, u, w} J) hiso.symm
    (isFiniteLocallyConstant_coequalizer J _ _ hcop' hcop)

/-- The finite locally constant sheaves of sets are closed under limits indexed by a finite
category `K`. -/
instance isClosedUnderLimitsOfShape_isFiniteLocallyConstantSetSheaf
    (K : Type) [SmallCategory K] [FinCategory K] :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (isFiniteLocallyConstantSetSheaf.{v, u, w} J) K :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨D, hD⟩
    exact isFiniteLocallyConstant_limit J D hD)

/-- The finite locally constant sheaves of sets are closed under colimits indexed by a finite
category `K`. -/
instance isClosedUnderColimitsOfShape_isFiniteLocallyConstantSetSheaf
    (K : Type) [SmallCategory K] [FinCategory K] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (isFiniteLocallyConstantSetSheaf.{v, u, w} J) K :=
  ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
    rintro _ ⟨D, hD⟩
    exact isFiniteLocallyConstant_colimit J D hD)

/-- The finite locally constant sheaves of sets are closed under finite limits. -/
instance isClosedUnderFiniteLimits_isFiniteLocallyConstantSetSheaf :
    ObjectProperty.IsClosedUnderFiniteLimits
      (isFiniteLocallyConstantSetSheaf.{v, u, w} J) where

/-- The finite locally constant sheaves of sets are closed under finite colimits. -/
instance isClosedUnderFiniteColimits_isFiniteLocallyConstantSetSheaf :
    ObjectProperty.IsClosedUnderFiniteColimits
      (isFiniteLocallyConstantSetSheaf.{v, u, w} J) where

/-- On a site, the finite locally constant sheaves of sets are closed under finite limits and
under finite colimits inside the category of all sheaves of sets.

The clause of the tag proved here is part (1), about sheaves of *sets* whose local constant
values are finite sets. It is not an instance of part (3), which is
`Stacks.ConstantSheaf.isWeakSerreClass_isFiniteTypeLocallyConstantModuleSheaf`: there the
finiteness is finiteness of type over a Noetherian coefficient ring, here it is finiteness of the
local value itself. -/
@[stacks 093U "sets"]
theorem isClosedUnderFiniteLimits_and_finiteColimits_isFiniteLocallyConstantSetSheaf :
    ObjectProperty.IsClosedUnderFiniteLimits
        (isFiniteLocallyConstantSetSheaf.{v, u, w} J) ∧
      ObjectProperty.IsClosedUnderFiniteColimits
        (isFiniteLocallyConstantSetSheaf.{v, u, w} J) :=
  ⟨inferInstance, inferInstance⟩

/-- A limit of finite locally constant sheaves of sets over a finite index category whose objects
live in an arbitrary universe is finite locally constant.

The closure instances above are stated for index categories in `Type`, which is what Mathlib's
`ObjectProperty.IsClosedUnderFiniteLimits` asks for; a finite category in any universe is
equivalent to one in `Type` by `CategoryTheory.FinCategory.equivAsType`, and closure under limits
of a shape only depends on the shape up to equivalence. -/
theorem isFiniteLocallyConstant_limit_of_finCategory {K : Type*} [SmallCategory K] [FinCategory K]
    (D : K ⥤ Sheaf J (Type (max u v w))) [HasLimit D]
    (h : ∀ k, IsFiniteLocallyConstant J (D.obj k)) :
    IsFiniteLocallyConstant J (limit D) := by
  have : ObjectProperty.IsClosedUnderLimitsOfShape
      (isFiniteLocallyConstantSetSheaf.{v, u, w} J) K :=
    (isClosedUnderLimitsOfShape_isFiniteLocallyConstantSetSheaf J
      (FinCategory.AsType K)).of_equivalence (FinCategory.equivAsType K)
  exact ObjectProperty.prop_limit (isFiniteLocallyConstantSetSheaf.{v, u, w} J) D h

/-- A colimit of finite locally constant sheaves of sets over a finite index category whose
objects live in an arbitrary universe is finite locally constant. -/
theorem isFiniteLocallyConstant_colimit_of_finCategory {K : Type*} [SmallCategory K]
    [FinCategory K] (D : K ⥤ Sheaf J (Type (max u v w))) [HasColimit D]
    (h : ∀ k, IsFiniteLocallyConstant J (D.obj k)) :
    IsFiniteLocallyConstant J (colimit D) := by
  have : ObjectProperty.IsClosedUnderColimitsOfShape
      (isFiniteLocallyConstantSetSheaf.{v, u, w} J) K :=
    (isClosedUnderColimitsOfShape_isFiniteLocallyConstantSetSheaf J
      (FinCategory.AsType K)).of_equivalence (FinCategory.equivAsType K)
  exact ObjectProperty.prop_colimit (isFiniteLocallyConstantSetSheaf.{v, u, w} J) D h

/-- The category of finite locally constant sheaves of sets on a site has finite products, being
closed under them inside the category of all sheaves of sets. -/
instance hasFiniteProducts_isFiniteLocallyConstantSetSheaf :
    HasFiniteProducts (isFiniteLocallyConstantSetSheaf.{v, u, w} J).FullSubcategory :=
  inferInstance

end Main

end Stacks.ConstantSheaf
