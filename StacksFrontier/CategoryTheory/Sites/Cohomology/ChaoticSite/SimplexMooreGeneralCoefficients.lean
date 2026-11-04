module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekFreeModuleBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two coefficient inputs for the Moore complex over `Δ`, at arbitrary abelian coefficients

Let `Δ = SimplexCategory` carry the chaotic topology, so that a presheaf on `Δ` with values in an
abelian category `A` is a simplicial object of `A` and the lower shriek to a point is the colimit
over `Δᵒᵖ`. The development of
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/MooreCochainComplex.lean` is stated for
arbitrary abelian coefficients and carries, as hypotheses, the two facts the coefficient category
has to supply for a presheaf `ℱ`:

* the colimit injection at `U_0` presents `colim ℱ` as a cokernel of the degree-one Moore
  differential, and
* the Moore complex of `ℱ(U_•)` has no homology in positive degrees.

This file discharges both at `C = Δ` with the tautological cosimplicial object `U_• = 𝟭 Δ`, for
*arbitrary* abelian coefficients — the existing discharges
(`Stacks.ChaoticSite.colimitι_isColimit` and
`Stacks.ChaoticSite.isZero_cosimplicialHomology_projective_succ`) are at abelian-group
coefficients, where they go through the free abelian presheaves on representables.

The first is the classical statement that the colimit of a simplicial object is the coequalizer of
`d₀` and `d₁`; over `Δ` it needs no hypothesis beyond the existence of the colimit, because `⦋0⦌`
receives a morphism from every object of `Δ` and any two morphisms `⦋0⦌ ⟶ ⦋k⦌` are the two ends of
a single `1`-simplex of `Δ`, namely of the morphism `⦋1⦌ ⟶ ⦋k⦌` picking out the ordered pair of
their values.

The second is proved for the *free* simplicial objects `∐_{Mor_Δ(-, ⦋m⦌)} Y`, which are the values
of the left adjoint of evaluation at `op ⦋m⦌`: such an object is the product, in the sense of
[Stacks, Tag 017C], of the standard simplex `Mor_Δ(-, ⦋m⦌)` with the constant simplicial object on
`Y`, the standard simplex is contractible ([Stacks, Tag 08QD]), and multiplying by a contractible
simplicial set does not change the homology of the Moore complex. The Moore complex of a constant
simplicial object is the alternating constant complex, which is exact away from degree zero.

## Main definitions

* `Stacks.ChaoticSite.SimplexValued.ofLe`: the morphism `⦋1⦌ ⟶ m` picking out an ordered pair of
  vertices of `m`.
* `Stacks.ChaoticSite.SimplexValued.coconeOfDOneZero`: the cocone on a simplicial object attached
  to a morphism out of its degree-zero term which kills `d₀ - d₁`.
* `Stacks.ChaoticSite.SimplexValued.freeSimplicial`: the free simplicial object
  `∐_{Mor_Δ(-, m)} Y` on an object `Y` of the coefficient category, that is, the value at `Y` of
  the left adjoint of evaluation at `op m`.

## Main results

* `Stacks.ChaoticSite.SimplexValued.colimitIotaZeroIsColimit`: **the colimit over `Δᵒᵖ` is the
  cokernel of the degree-one Moore differential** `X(δ₀) - X(δ₁)`, the projection being the colimit
  injection at `⦋0⦌`. This is the first coefficient input.
* `Stacks.ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_freeSimplicial_succ`:
  **the Moore complex of a free simplicial object has no homology in positive degrees.** This is
  the second coefficient input, on the objects the general case reduces to.
* `Stacks.ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_succ_of_coproduct`:
  positive-degree vanishing passes to coproducts, when coproducts of the given shape are exact.
* `Stacks.ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_of_retract`:
  positive-degree vanishing passes to retracts.
* `Stacks.ChaoticSite.SimplexValued.quasiIso_mooreCochainAugmentation_freeSimplicial` and
  `Stacks.ChaoticSite.SimplexValued.quasiIso_mooreCochainAugmentation_coproduct_freeSimplicial`:
  the two inputs combined, through
  `Stacks.ChaoticSite.GeneralValued.quasiIso_mooreCochainAugmentation`: the extended Moore complex
  of a free simplicial object, and of a coproduct of such, is a resolution of its colimit.

## Implementation notes

**The cokernel presentation.** The cocone produced from `g : X_0 ⟶ T` with `(X(δ₀) - X(δ₁)) ≫ g`
zero has, at `n`, the component `X(ε) ≫ g` for `ε : ⦋0⦌ ⟶ n` the constant morphism at the vertex
`0`. Both the naturality of that family and the uniqueness of the induced morphism rest on the one
lemma `map_op_comp_eq_of_d_zero_comp_eq`: *any two* morphisms `u, v : ⦋0⦌ ⟶ m` satisfy
`X(u) ≫ g = X(v) ≫ g`. That holds because, after replacing `u` and `v` by the constant morphisms
at their values `a` and `b` and ordering the two values, both are obtained from the single morphism
`w = ofLe : ⦋1⦌ ⟶ m` by composing with the two cofaces `⦋0⦌ ⟶ ⦋1⦌`, so the relation is exactly the
hypothesis read through `X(w)`. No choice and no point resolution enters; in particular nothing
here is specific to the coefficient category beyond its being preadditive.

**The free simplicial objects.** `freeSimplicial m Y` is written as the copower
`Functor.copower` of the constant simplicial object on `Y` by the simplicial set
`Mor_Δ(-, m) = (𝟭 Δ).op ⋙ yoneda.obj m`, so that the product of [Stacks, Tag 017C] and its
projection of [Stacks, Tag 017E] (2) apply to it with no comparison map at all. It is the same
object as `(evaluationLeftAdjoint A (op m)).obj Y`, the value of the left adjoint of evaluation at
`op m`, whose value at `j` is the coproduct of copies of `Y` indexed by `op m ⟶ j`; that
identification is *not* recorded here, because the two index sets `op m ⟶ j` and
`Mor_Δ(j, m)` are compared by Mathlib's `yoneda_obj_obj_eq_hom` unification hint, whose pattern
asks for an argument of the syntactic form `op _` and so does not fire through the restriction
along `(𝟭 Δ).op`. Nothing below needs it: the universal property that makes these objects the
projective generators is the adjunction, which is about morphisms out of them.

The homology statement is `CategoryTheory.SimplicialObject.isIso_homologyMap_copowerProj` — a
functor inverting simplicial homotopy equivalences inverts the projection off a contractible
factor — applied with the contraction
`Stacks.ChaoticSite.isPointResolution_id_simplexCategory` of the standard simplex, and
`AlgebraicTopology.alternatingFaceMapComplexConst` together with
`ChainComplex.alternatingConst_exactAt` for the target.

**Coproducts.** The coproduct statement carries `HasExactColimitsOfShape (Discrete ι) A`, that is
Grothendieck's AB4 for the shape, and that hypothesis is not an artefact: the homology of a
coproduct of complexes is the coproduct of their homologies only when coproducts are exact. At
abelian-group coefficients, where
`Stacks.ChaoticSite.isZero_cosimplicialHomology_directSum_succ` does the same work, it holds
automatically. The alternative route — taking coproducts of *chain homotopy equivalences*, which
needs no exactness — is not available here: the simplicial homotopy equivalence of a contractible
factor is `CategoryTheory.SimplicialObject.homotopyEquivalences`, defined through the equivalence
relation generated by the existence of a homotopy, and chains of unbounded length over an infinite
index set cannot be combined into one. This is the same obstruction that forces the finiteness
hypothesis on part (1) of [Stacks, Tag 08Q4].

**Universes.** `Δ` is a `Type` with `Type`-valued homs, so the simplicial sets involved are
`Type 0`-valued and the coefficient category needs only `HasCoproducts.{0}`; the coefficient
category itself lives in an arbitrary universe, unlike the abelian-group-valued chain, which is
single-universe.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD), the contractibility of
  the standard simplices.
* [Stacks Project, Tag 017C](https://stacks.math.columbia.edu/tag/017C), the product of a
  simplicial set with a simplicial object.
* [Stacks Project, Tag 017E](https://stacks.math.columbia.edu/tag/017E), its projection.
* [Stacks Project, Tag 08Q4](https://stacks.math.columbia.edu/tag/08Q4), homotopies and products.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

namespace Stacks.ChaoticSite.SimplexValued

/-! ### Ordered pairs of vertices -/

section OfLe

/-- **The morphism `⦋1⦌ ⟶ m` picking out an ordered pair of vertices of `m`**: the monotone map
sending `0` to `a` and `1` to `b`. This is `SimplexCategory.mkOfLe` written for an arbitrary object
`m` of `Δ` in place of `⦋k⦌`. -/
def ofLe {m : SimplexCategory} {a b : Fin (m.len + 1)} (h : a ≤ b) :
    (⦋1⦌ : SimplexCategory) ⟶ m :=
  SimplexCategory.Hom.mk
    { toFun := fun | 0 => a | 1 => b
      monotone' := fun | 0, 0, _ | 1, 1, _ => le_rfl | 0, 1, _ => h }

/-- The vertex `0` of `ofLe h` is the smaller of the two. -/
@[simp]
lemma ofLe_apply_zero {m : SimplexCategory} {a b : Fin (m.len + 1)} (h : a ≤ b) :
    (ofLe h).toOrderHom 0 = a :=
  rfl

/-- The vertex `1` of `ofLe h` is the larger of the two. -/
@[simp]
lemma ofLe_apply_one {m : SimplexCategory} {a b : Fin (m.len + 1)} (h : a ≤ b) :
    (ofLe h).toOrderHom 1 = b :=
  rfl

/-- The coface `δ₁ : ⦋0⦌ ⟶ ⦋1⦌`, which hits the vertex `0`, cuts `ofLe h` down to the constant
morphism at the smaller vertex. -/
lemma δ_one_comp_ofLe {m : SimplexCategory} {a b : Fin (m.len + 1)} (h : a ≤ b) :
    SimplexCategory.δ (1 : Fin 2) ≫ ofLe h = SimplexCategory.const ⦋0⦌ m a := by
  rw [SimplexCategory.δ_one_eq_const, SimplexCategory.const_comp, ofLe_apply_zero]

/-- The coface `δ₀ : ⦋0⦌ ⟶ ⦋1⦌`, which hits the vertex `1`, cuts `ofLe h` down to the constant
morphism at the larger vertex. -/
lemma δ_zero_comp_ofLe {m : SimplexCategory} {a b : Fin (m.len + 1)} (h : a ≤ b) :
    SimplexCategory.δ (0 : Fin 2) ≫ ofLe h = SimplexCategory.const ⦋0⦌ m b := by
  rw [SimplexCategory.δ_zero_eq_const, SimplexCategory.const_comp, ofLe_apply_one]

end OfLe

/-! ### The colimit over `Δᵒᵖ` as a cokernel of the degree-one Moore differential -/

section Cokernel

variable {A : Type*} [Category* A] [Preadditive A]

omit [Preadditive A] in
/-- **Any two morphisms `⦋0⦌ ⟶ m` restrict identically into a morphism out of `X_0` equalizing the
two cofaces.** The two morphisms are the constant morphisms at their values, and after ordering
those values both are a coface of the single morphism `ofLe : ⦋1⦌ ⟶ m`, so the asserted equality is
the hypothesis read through that morphism. -/
theorem map_op_comp_eq_of_d_zero_comp_eq {X : SimplexCategoryᵒᵖ ⥤ A} {T : A}
    (g : X.obj (op ⦋0⦌) ⟶ T)
    (hg : X.map (SimplexCategory.δ (0 : Fin 2)).op ≫ g =
      X.map (SimplexCategory.δ (1 : Fin 2)).op ≫ g)
    {m : SimplexCategory} (u v : (⦋0⦌ : SimplexCategory) ⟶ m) :
    X.map u.op ≫ g = X.map v.op ≫ g := by
  have key : ∀ (a b : Fin (m.len + 1)) (h : a ≤ b),
      X.map (SimplexCategory.const ⦋0⦌ m a).op ≫ g =
        X.map (SimplexCategory.const ⦋0⦌ m b).op ≫ g := by
    intro a b h
    rw [← δ_one_comp_ofLe h, ← δ_zero_comp_ofLe h, op_comp, op_comp, X.map_comp, X.map_comp,
      Category.assoc, Category.assoc, hg]
  obtain ⟨a, rfl⟩ := SimplexCategory.exists_eq_const_of_zero u
  obtain ⟨b, rfl⟩ := SimplexCategory.exists_eq_const_of_zero v
  rcases le_total a b with h | h
  exacts [key a b h, (key b a h).symm]

/-- **The cocone on a simplicial object attached to a morphism out of its degree-zero term which
equalizes the two cofaces**: over `n` it is the restriction along the constant morphism
`⦋0⦌ ⟶ n` at the vertex `0`, which the hypothesis makes independent of every choice. -/
def coconeOfDOneZero (X : SimplexCategoryᵒᵖ ⥤ A) {T : A} (g : X.obj (op ⦋0⦌) ⟶ T)
    (hg : X.map (SimplexCategory.δ (0 : Fin 2)).op ≫ g =
      X.map (SimplexCategory.δ (1 : Fin 2)).op ≫ g) :
    Cocone X where
  pt := T
  ι :=
    { app n := X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op ≫ g
      naturality n n' φ := by
        change X.map φ ≫ X.map (SimplexCategory.const ⦋0⦌ n'.unop 0).op ≫ g =
          (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op ≫ g) ≫ 𝟙 T
        rw [Category.comp_id, ← Category.assoc, ← X.map_comp]
        exact map_op_comp_eq_of_d_zero_comp_eq g hg
          (SimplexCategory.const ⦋0⦌ n'.unop 0 ≫ φ.unop)
          (SimplexCategory.const ⦋0⦌ n.unop 0) }

/-- A morphism out of the degree-zero term of the Moore complex over `𝟭 Δ` which kills the
degree-one differential equalizes the two cofaces: the differential is their difference. -/
lemma eq_of_d_one_zero_comp {X : SimplexCategoryᵒᵖ ⥤ A} {T : A}
    (g : ((GeneralValued.cosimplicialMooreComplex A (𝟭 SimplexCategory)).obj X).X 0 ⟶ T)
    (hg : ((GeneralValued.cosimplicialMooreComplex A (𝟭 SimplexCategory)).obj X).d 1 0 ≫ g = 0) :
    X.map (SimplexCategory.δ (0 : Fin 2)).op ≫ g =
      X.map (SimplexCategory.δ (1 : Fin 2)).op ≫ g := by
  rwa [GeneralValued.cosimplicialMooreComplex_obj_d_one_zero, Preadditive.sub_comp,
    sub_eq_zero] at hg

variable [HasColimitsOfShape SimplexCategoryᵒᵖ A]

/-- **The colimit of a simplicial object over `Δᵒᵖ` is a cokernel of `X(δ₀) - X(δ₁)`**, the
projection being the colimit injection at `⦋0⦌`. By
`Stacks.ChaoticSite.GeneralValued.cosimplicialMooreComplex_obj_d_one_zero` the morphism being
killed is the degree-one differential of the Moore complex of `X` over the tautological
cosimplicial object `𝟭 Δ`, so this is the first of the two inputs the coefficient category supplies
to `Stacks.ChaoticSite.GeneralValued.quasiIso_mooreCochainAugmentation`. Every object of `Δ`
receives a morphism from `⦋0⦌`, and any two such restrict identically into a morphism killing that
differential. -/
def colimitIotaZeroIsColimit (X : SimplexCategoryᵒᵖ ⥤ A) :
    IsColimit (CokernelCofork.ofπ
      (colimit.ι X (Opposite.op ((𝟭 SimplexCategory).obj (SimplexCategory.mk 0))))
      (Stacks.ChaoticSite.GeneralValued.d_one_zero_comp_colimitι (𝟭 SimplexCategory) X)) :=
  Cofork.IsColimit.mk _
    (fun S ↦ colimit.desc X
      (coconeOfDOneZero X S.π (eq_of_d_one_zero_comp S.π (CokernelCofork.condition S))))
    (fun S ↦ by
      refine (colimit.ι_desc _ _).trans ?_
      change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op ≫ S.π = S.π
      rw [SimplexCategory.const_eq_id]
      simp)
    (fun S m hm ↦ by
      have hm' : colimit.ι X (Opposite.op (SimplexCategory.mk 0)) ≫ m = S.π := hm
      refine colimit.hom_ext fun n ↦ Eq.trans ?_ (colimit.ι_desc
        (coconeOfDOneZero X S.π (eq_of_d_one_zero_comp S.π (CokernelCofork.condition S))) n).symm
      rw [← colimit.w X (SimplexCategory.const ⦋0⦌ n.unop 0).op, Category.assoc, hm']
      rfl)

end Cokernel

/-! ### The free simplicial objects on an object of the coefficient category -/

section FreeSimplicial

variable {A : Type*} [Category* A] [HasCoproducts.{0} A]

/-- **The free simplicial object on an object `Y` of the coefficient category at an object `m` of
`Δ`**: the simplicial object `n ↦ ∐_{Mor_Δ(n, m)} Y`, that is the product of the standard simplex
on `m` with the constant simplicial object on `Y` in the sense of [Stacks, Tag 017C]. It is the
value at `Y` of the left adjoint of evaluation at `op m`, maps out of it being the morphisms
`Y ⟶ ℱ(m)`. -/
abbrev freeSimplicial (m : SimplexCategory) (Y : A) : SimplexCategoryᵒᵖ ⥤ A :=
  ((Functor.const SimplexCategoryᵒᵖ).obj Y).copower ((𝟭 SimplexCategory).op ⋙ yoneda.obj m)

/-- **The projection of the free simplicial object onto the constant simplicial object**, the
identity of `Y` on each summand. This is the projection of [Stacks, Tag 017E] (2) off the standard
simplex factor. -/
abbrev freeSimplicialProj (m : SimplexCategory) (Y : A) :
    freeSimplicial m Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj Y :=
  ((Functor.const SimplexCategoryᵒᵖ).obj Y).copowerProj
    ((𝟭 SimplexCategory).op ⋙ yoneda.obj m)

variable [Abelian A]

/-- **The Moore complex of a free simplicial object has no homology in positive degrees.** The free
simplicial object is the product of the standard simplex on `m` with the constant simplicial object
on `Y`; the standard simplex is contractible, so the projection off it is a homology isomorphism of
Moore complexes, and the Moore complex of a constant simplicial object is the alternating constant
complex, which is exact away from degree zero.

This is the second of the two inputs the coefficient category supplies to
`Stacks.ChaoticSite.GeneralValued.quasiIso_mooreCochainAugmentation`, on the objects to which the
general case reduces. -/
@[sga "4 Vbis 2.3.9" "partial"]
theorem isZero_homology_alternatingFaceMapComplex_freeSimplicial_succ
    (m : SimplexCategory) (Y : A) (n : ℕ) :
    IsZero (((alternatingFaceMapComplex A).obj (freeSimplicial m Y)).homology (n + 1)) := by
  have hconst : IsZero (((alternatingFaceMapComplex A).obj
      ((Functor.const SimplexCategoryᵒᵖ).obj Y)).homology (n + 1)) :=
    IsZero.of_iso
      ((ChainComplex.alternatingConst_exactAt Y (n + 1) (Nat.succ_ne_zero n)).isZero_homology)
      ((HomologicalComplex.homologyFunctor A (ComplexShape.down ℕ) (n + 1)).mapIso
        (alternatingFaceMapComplexConst.app Y))
  have hproj := SimplicialObject.isIso_homologyMap_copowerProj
    ((Functor.const SimplexCategoryᵒᵖ).obj Y) (n + 1)
    ((𝟭 SimplexCategory).op ⋙ yoneda.obj m)
    (Stacks.ChaoticSite.isPointResolution_id_simplexCategory m)
  exact IsZero.of_iso hconst (asIso (HomologicalComplex.homologyMap
    ((alternatingFaceMapComplex A).map (freeSimplicialProj m Y)) (n + 1)))

end FreeSimplicial

/-! ### Stability of the vanishing under isomorphisms, retracts and coproducts -/

section Stability

variable {A : Type*} [Category* A] [Abelian A]

/-- Vanishing of the homology of the Moore complex in a fixed degree is invariant under
isomorphism of the simplicial object. -/
theorem isZero_homology_alternatingFaceMapComplex_of_iso {X Y : SimplexCategoryᵒᵖ ⥤ A} (e : X ≅ Y)
    (n : ℕ) (h : IsZero (((alternatingFaceMapComplex A).obj Y).homology n)) :
    IsZero (((alternatingFaceMapComplex A).obj X).homology n) :=
  IsZero.of_iso h
    ((alternatingFaceMapComplex A ⋙
      HomologicalComplex.homologyFunctor A (ComplexShape.down ℕ) n).mapIso e)

/-- **Vanishing of the homology of the Moore complex in a fixed degree passes to retracts**: the
identity of the retract factors through a zero object. -/
theorem isZero_homology_alternatingFaceMapComplex_of_retract {X Y : SimplexCategoryᵒᵖ ⥤ A}
    (i : X ⟶ Y) (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X) (n : ℕ)
    (h : IsZero (((alternatingFaceMapComplex A).obj Y).homology n)) :
    IsZero (((alternatingFaceMapComplex A).obj X).homology n) := by
  let T : (SimplexCategoryᵒᵖ ⥤ A) ⥤ A :=
    alternatingFaceMapComplex A ⋙ HomologicalComplex.homologyFunctor A (ComplexShape.down ℕ) n
  have hT : IsZero (T.obj Y) := h
  rw [IsZero.iff_id_eq_zero]
  have h₁ : T.map i ≫ T.map r = 𝟙 (T.obj X) := by rw [← T.map_comp, hir, T.map_id]
  have h₂ : T.map i ≫ T.map r = 0 := by rw [hT.eq_of_tgt (T.map i) 0, zero_comp]
  exact h₁.symm.trans h₂

/-- A short complex of functors is exact as soon as it is exact at every object: homology in a
functor category is computed objectwise, evaluation at an object being an exact functor. -/
private lemma exact_of_exact_map_evaluation {J : Type*} [Category* J]
    (S : ShortComplex (J ⥤ A))
    (h : ∀ j : J, (S.map ((evaluation J A).obj j)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ fun j ↦ ?_
  have hl : PreservesFiniteLimits ((evaluation J A).obj j) := ⟨fun _ _ _ ↦ inferInstance⟩
  have hc : PreservesFiniteColimits ((evaluation J A).obj j) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).1 (h j))
    (S.mapHomologyIso ((evaluation J A).obj j)).symm

variable {ι : Type*} [HasColimitsOfShape (Discrete ι) A]

/-- The evaluation of a family of simplicial objects in a fixed degree, as a diagram on
`Discrete ι`. The coproduct of the family, evaluated in that degree, is its colimit. -/
private abbrev degreeDiagram (X : ι → (SimplexCategoryᵒᵖ ⥤ A)) (p : ℕ) : Discrete ι ⥤ A :=
  Discrete.functor X ⋙
    (evaluation SimplexCategoryᵒᵖ A).obj (Opposite.op (SimplexCategory.mk p))

/-- The short complex of the degree `n + 1` Moore differentials of a family of simplicial objects,
read in the functor category on `Discrete ι`. -/
private def degreeShortComplex (X : ι → (SimplexCategoryᵒᵖ ⥤ A)) (n : ℕ) :
    ShortComplex (Discrete ι ⥤ A) :=
  ShortComplex.mk
    (Discrete.natTrans (F := degreeDiagram X (n + 2)) (G := degreeDiagram X (n + 1))
      fun i ↦ ((alternatingFaceMapComplex A).obj (X i.as)).d (n + 2) (n + 1))
    (Discrete.natTrans (F := degreeDiagram X (n + 1)) (G := degreeDiagram X n)
      fun i ↦ ((alternatingFaceMapComplex A).obj (X i.as)).d (n + 1) n)
    (by
      ext i
      simpa using ((alternatingFaceMapComplex A).obj (X i.as)).d_comp_d (n + 2) (n + 1) n)

variable [HasExactColimitsOfShape (Discrete ι) A]

/-- **Vanishing of the homology of the Moore complex in a fixed positive degree passes to
coproducts**, when coproducts of that shape are exact in the coefficient category — Grothendieck's
AB4 for the shape, which holds for abelian groups and for modules. Degreewise the Moore complex of
the coproduct is the coproduct of the Moore complexes, the summand inclusions being chain maps, so
the three-term complex computing the homology is the colimit over `Discrete ι` of the three-term
complexes of the summands. -/
theorem isZero_homology_alternatingFaceMapComplex_succ_of_coproduct
    (X : ι → (SimplexCategoryᵒᵖ ⥤ A))
    (h : ∀ (i : ι) (n : ℕ),
      IsZero (((alternatingFaceMapComplex A).obj (X i)).homology (n + 1)))
    (n : ℕ) :
    IsZero (((alternatingFaceMapComplex A).obj (∐ X)).homology (n + 1)) := by
  have hex := fun K : ChainComplex A ℕ ↦ HomologicalComplex.exactAt_iff' K (n + 2) (n + 1) n
    (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, hex]
  have hS : (degreeShortComplex X n).Exact :=
    exact_of_exact_map_evaluation _ fun j ↦
      (hex _).1 ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (h j.as n))
  have hc : ∀ p : ℕ, IsColimit
      (((evaluation SimplexCategoryᵒᵖ A).obj (Opposite.op (SimplexCategory.mk p))).mapCocone
        (colimit.cocone (Discrete.functor X))) :=
    fun _ ↦ isColimitOfPreserves _ (colimit.isColimit _)
  exact Limits.colim.exact_mapShortComplex hS (hc (n + 2)) (hc (n + 1)) (hc n)
    (((alternatingFaceMapComplex A).obj (∐ X)).d (n + 2) (n + 1))
    (((alternatingFaceMapComplex A).obj (∐ X)).d (n + 1) n)
    (fun j ↦ ((alternatingFaceMapComplex A).map
      (colimit.ι (Discrete.functor X) j)).comm (n + 2) (n + 1))
    (fun j ↦ ((alternatingFaceMapComplex A).map
      (colimit.ι (Discrete.functor X) j)).comm (n + 1) n)

end Stability

/-! ### The two inputs combined -/

section Combined

variable {A : Type*} [Category* A] [Abelian A] [HasColimitsOfShape SimplexCategoryᵒᵖ A]

omit [HasColimitsOfShape SimplexCategoryᵒᵖ A] in
/-- At `U_• = 𝟭 Δ` the Moore complex of the evaluation on `U_•` is the alternating-face-map complex
itself, at arbitrary coefficients: evaluation on `𝟭` is the identity functor. -/
theorem cosimplicialMooreComplex_id :
    GeneralValued.cosimplicialMooreComplex A (𝟭 SimplexCategory) = alternatingFaceMapComplex A :=
  rfl

/-- **The extended Moore complex of a simplicial object is a resolution of its colimit as soon as
its positive homology vanishes**, at the site `Δ` with the tautological cosimplicial object
`𝟭 Δ`: the cokernel presentation of the colimit injection is `colimitIotaZeroIsColimit`, which
needs no hypothesis. -/
theorem quasiIso_mooreCochainAugmentation_of_isZero (X : SimplexCategoryᵒᵖ ⥤ A)
    (hzero : ∀ n : ℕ, IsZero (((alternatingFaceMapComplex A).obj X).homology (n + 1))) :
    QuasiIso ((GeneralValued.mooreCochainAugmentation (𝟭 SimplexCategory)).app X) :=
  GeneralValued.quasiIso_mooreCochainAugmentation (𝟭 SimplexCategory) X hzero
    (colimitIotaZeroIsColimit X)

variable [HasCoproducts.{0} A]

/-- **The extended Moore complex of a free simplicial object is a resolution of its colimit.** Both
coefficient inputs are discharged: the positive homology vanishes by
`isZero_homology_alternatingFaceMapComplex_freeSimplicial_succ` and the colimit injection at `⦋0⦌`
is a cokernel of the degree-one differential by `colimitIotaZeroIsColimit`. -/
theorem quasiIso_mooreCochainAugmentation_freeSimplicial (m : SimplexCategory) (Y : A) :
    QuasiIso ((GeneralValued.mooreCochainAugmentation (𝟭 SimplexCategory)).app
      (freeSimplicial m Y)) :=
  quasiIso_mooreCochainAugmentation_of_isZero (freeSimplicial m Y)
    (isZero_homology_alternatingFaceMapComplex_freeSimplicial_succ m Y)

variable {ι : Type*} [HasColimitsOfShape (Discrete ι) A]
  [HasExactColimitsOfShape (Discrete ι) A]

omit [HasCoproducts A] in
/-- **The extended Moore complex of a coproduct of simplicial objects with vanishing positive
homology is a resolution of its colimit**, when coproducts of that shape are exact in the
coefficient category. -/
theorem quasiIso_mooreCochainAugmentation_coproduct (X : ι → (SimplexCategoryᵒᵖ ⥤ A))
    (h : ∀ (i : ι) (n : ℕ),
      IsZero (((alternatingFaceMapComplex A).obj (X i)).homology (n + 1))) :
    QuasiIso ((GeneralValued.mooreCochainAugmentation (𝟭 SimplexCategory)).app (∐ X)) :=
  quasiIso_mooreCochainAugmentation_of_isZero (∐ X)
    (isZero_homology_alternatingFaceMapComplex_succ_of_coproduct X h)

/-- **The extended Moore complex of a coproduct of free simplicial objects is a resolution of its
colimit**, when coproducts of that shape are exact in the coefficient category. These are the
objects a projective presentation of a simplicial object of the coefficient category is built
from. -/
theorem quasiIso_mooreCochainAugmentation_coproduct_freeSimplicial
    (m : ι → SimplexCategory) (Y : ι → A) :
    QuasiIso ((GeneralValued.mooreCochainAugmentation (𝟭 SimplexCategory)).app
      (∐ fun i ↦ freeSimplicial (m i) (Y i))) :=
  quasiIso_mooreCochainAugmentation_coproduct _
    fun i ↦ isZero_homology_alternatingFaceMapComplex_freeSimplicial_succ (m i) (Y i)

end Combined

end Stacks.ChaoticSite.SimplexValued

end
