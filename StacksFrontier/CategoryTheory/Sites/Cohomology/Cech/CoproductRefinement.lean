module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement
import StacksCore.Tactic.StacksAttribute

/-!
# Refining a family of morphisms by its coproduct

Let `{U_i → T}_{i ∈ I}` be a family of morphisms with fixed target whose index type admits a
coproduct of the `U_i`. The component inclusions `U_i → ∐ U_i` exhibit the family as a
refinement of the singleton family `{∐ U_i → T}`, which is Stacks 03FI part (2). When the
ambient category is finitary extensive, the index type is finite and the coefficient presheaf
preserves finite products, the induced map of Čech complexes of Stacks 03F4 is an isomorphism,
which is the abstract form of the comparison in Stacks 03FI part (3).

## Main definitions

* `Stacks.CechSite.coproductRefinement`: the refinement of a family by the single morphism from
  the coproduct of its members.

## Main results

* `Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts`: for a finite-product
  preserving presheaf on a finitary extensive category, the Čech complex of a finite family
  agrees with the Čech complex of its coproduct morphism.

## Implementation notes

The isomorphism is checked degreewise. In degree `n` the comparison map is the canonical map
from the presheaf evaluated at the `(n + 1)`-fold power of the coproduct to the product, over
all `(n + 1)`-tuples of indices, of the presheaf evaluated at the corresponding iterated fibre
product. That power is again a coproduct, indexed by tuples, of those fibre products: this is
proved by induction on `n` from the universality of finite coproducts in a finitary
pre-extensive category, splitting off one factor of the power as a product over a terminal
object.

## References

* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 03F4](https://stacks.math.columbia.edu/tag/03F4)
-/

@[expose] public section

universe w v v' u u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits

/-- The component inclusions of a coproduct exhibit a family of morphisms with fixed target as
a refinement of the singleton family given by the induced morphism from the coproduct. -/
@[stacks 03FI "part (2)"]
noncomputable def coproductRefinement {C : Type u} [Category.{v} C]
    {T : C} (E : PreZeroHypercover.{w} T) [HasCoproduct E.X] :
    E.HomOver (PreZeroHypercover.singleton (Sigma.desc E.f)) (𝟙 T) where
  s₀ _ := PUnit.unit
  h₀ i := Sigma.ι E.X i
  w₀ i := by
    simp only [PreZeroHypercover.singleton_f, Category.comp_id]
    exact Sigma.ι_desc E.f i

section CechComparison

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- The projection of a product indexed by `Fin (n + 1)` onto the product of its last `n`
factors. -/
private noncomputable abbrev productTailProjection {n : ℕ} (X : Fin (n + 1) → C) :
    ∏ᶜ X ⟶ ∏ᶜ (fun a : Fin n ↦ X a.succ) :=
  Pi.lift (fun a ↦ Pi.π X a.succ)

/-- A product indexed by `Fin (n + 1)` is the fibre product over the terminal object of its
first factor and the product of its last `n` factors. -/
private noncomputable def isLimit_splitProduct {n : ℕ} (X : Fin (n + 1) → C) :
    IsLimit (PullbackCone.mk (Pi.π X 0) (productTailProjection X)
      (show Pi.π X 0 ≫ terminal.from _ = productTailProjection X ≫ terminal.from _ from
        Subsingleton.elim _ _)) := by
  refine PullbackCone.IsLimit.mk _ (fun s ↦ Pi.lift (Fin.cases s.fst
    (fun a ↦ s.snd ≫ Pi.π _ a))) ?_ ?_ ?_
  · intro s
    simp
  · intro s
    apply Pi.hom_ext
    intro a
    simp [productTailProjection]
  · intro s m h₁ h₂
    apply Pi.hom_ext
    intro a
    induction a using Fin.cases with
    | zero => simpa using h₁
    | succ a =>
      simpa [productTailProjection] using congrArg (fun k ↦ k ≫ Pi.π _ a) h₂

-- `Fin.cases` is compiled from `Fin.induction`, whose recursion is a plain `def`, so the
-- reindexing equivalence of the inductive step below is not seen to send `0` to the split-off
-- index and `a.succ` to the `a`-th remaining one at `implicit` transparency; without that the
-- two sides of the pullback-cone conditions are not even recognised as composable.
attribute [local implicit_reducible] Fin.cases Fin.induction Fin.induction.go in
/-- In a finitary pre-extensive category, the `n`-fold power of a finite coproduct is the
coproduct, indexed by `n`-tuples of indices, of the corresponding products of the summands. -/
private theorem nonempty_isColimit_powerCofan [FinitaryPreExtensive C]
    {I : Type w} [Finite I] {X : I → C} (c : Cofan X) (hc : IsColimit c) (n : ℕ) :
    Nonempty (IsColimit (Cofan.mk (∏ᶜ (fun _ : Fin n ↦ c.pt))
      (fun i : Fin n → I ↦ Limits.Pi.map (f := fun a ↦ X (i a))
        (g := fun _ ↦ c.pt) (fun a ↦ c.inj (i a))))) := by
  induction n with
  | zero =>
    let e (i : Fin 0 → I) : (∏ᶜ (fun a ↦ X (i a))) ≅ ∏ᶜ (fun _ : Fin 0 ↦ c.pt) :=
      { hom := Limits.Pi.map (f := fun a ↦ X (i a)) (g := fun _ ↦ c.pt) (fun a ↦ c.inj (i a))
        inv := Pi.lift (fun a ↦ Fin.elim0 a)
        hom_inv_id := Pi.hom_ext _ _ fun a ↦ a.elim0
        inv_hom_id := Pi.hom_ext _ _ fun a ↦ a.elim0 }
    refine ⟨Cofan.IsColimit.mk _ (fun s ↦ (e default).inv ≫ s.inj default) ?_ ?_⟩
    · intro s i
      obtain rfl : i = default := Subsingleton.elim _ _
      show (e default).hom ≫ (e default).inv ≫ s.inj default = _
      simp
    · intro s m hm
      have h := hm default
      change (e default).hom ≫ m = s.inj default at h
      simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
        congrArg (fun k ↦ (e default).inv ≫ k) h
  | succ n ih =>
    let d := Cofan.mk (∏ᶜ (fun _ : Fin n ↦ c.pt))
      (fun i : Fin n → I ↦ Limits.Pi.map (f := fun a ↦ X (i a))
        (g := fun _ ↦ c.pt) (fun a ↦ c.inj (i a)))
    let e : I × (Fin n → I) ≃ (Fin (n + 1) → I) :=
      { toFun p := Fin.cases p.1 p.2
        invFun i := (i 0, fun a ↦ i a.succ)
        left_inv p := rfl
        right_inv i := by
          funext a
          induction a using Fin.cases <;> rfl }
    let k := Cofan.mk (∏ᶜ (fun _ : Fin (n + 1) ↦ c.pt))
      (fun i : Fin (n + 1) → I ↦ Limits.Pi.map (f := fun a ↦ X (i a))
        (g := fun _ ↦ c.pt) (fun a ↦ c.inj (i a)))
    apply ((Cofan.isColimitEquivOfEquiv e k).symm).nonempty_congr.mp
    refine IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
      (FinitaryPreExtensive.isUniversal_finiteCoproducts hc)
      (FinitaryPreExtensive.isUniversal_finiteCoproducts ih.some)
      (fun i ↦ terminal.from (X i)) (fun i : Fin n → I ↦ terminal.from (∏ᶜ (fun a ↦ X (i a))))
      (terminal.from c.pt) (terminal.from d.pt)
      (fun i j ↦ (PullbackCone.mk (Pi.π (fun a ↦ X (e (i, j) a)) 0)
        (productTailProjection (fun a ↦ X (e (i, j) a))) (Subsingleton.elim _ _)))
      (fun i j ↦ isLimit_splitProduct (fun a ↦ X (e (i, j) a)))
      (PullbackCone.mk (Pi.π (fun _ : Fin (n + 1) ↦ c.pt) 0)
        (productTailProjection (fun _ : Fin (n + 1) ↦ c.pt)) (Subsingleton.elim _ _))
      (isLimit_splitProduct (fun _ : Fin (n + 1) ↦ c.pt)) (Iso.refl _) ?_ ?_ ?_ ?_
    · intro i
      exact Subsingleton.elim _ _
    · intro i
      exact Subsingleton.elim _ _
    · intro i j
      simp [k, Cofan.inj, PullbackCone.fst, PullbackCone.mk]
      rfl
    · intro i j
      apply Pi.hom_ext
      intro a
      dsimp [k, d, Cofan.inj, PullbackCone.snd, PullbackCone.mk, productTailProjection]
      simp only [Category.id_comp, Category.assoc, Pi.map_π, Pi.lift_π]
      rw [Pi.lift_π_assoc (f := fun b : Fin n ↦ X (j b))]
      rfl

/-- The cofan in the slice category over `T` whose summands are the members of the family `E`
and whose vertex is the induced morphism from their coproduct. -/
private noncomputable def coproductOverCofan {T : C} (E : PreZeroHypercover.{w} T)
    [HasCoproduct E.X] : Cofan (fun i ↦ Over.mk (E.f i)) :=
  Cofan.mk (Over.mk (Sigma.desc E.f)) (fun i ↦ Over.homMk (Sigma.ι E.X i) (Sigma.ι_desc E.f i))

attribute [local implicit_reducible] coproductOverCofan

/-- The coproduct of a family of objects of `C` is also their coproduct in the slice category
over `T`, taken over the induced morphism from the coproduct. -/
private noncomputable def isColimit_coproductOverCofan {T : C} (E : PreZeroHypercover.{w} T)
    [HasCoproduct E.X] : IsColimit (coproductOverCofan E) :=
  isColimitOfReflects (Over.forget T)
    ((isColimitMapCoconeCofanMkEquiv (Over.forget T) _ _).symm (coproductIsCoproduct E.X))

/-- Along `coproductRefinement`, the map of iterated fibre products is the product, over the
tuple of indices, of the component inclusions into the coproduct. -/
private theorem cechProductMap_coproduct {T : C} (E : PreZeroHypercover.{w} T)
    [HasCoproduct E.X] (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    cechProductMap E (PreZeroHypercover.singleton.{w} (Sigma.desc E.f))
      (coproductRefinement E) n i =
    (Limits.Pi.map (f := fun a ↦ Over.mk (E.f (i a)))
      (g := fun _ : Fin (n + 1) ↦ Over.mk (Sigma.desc E.f))
      (fun a ↦ (coproductOverCofan E).inj (i a))).left := by
  let Q := ∏ᶜ (fun a ↦ Over.mk (E.f (i a)))
  let e : Over.mk (Q.hom ≫ 𝟙 T) ≅ Q := Over.isoMk (Iso.refl Q.left)
  let m : Over.mk (Q.hom ≫ 𝟙 T) ⟶
      ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk (Sigma.desc E.f)) :=
    Pi.lift (fun a ↦ Over.homMk
      ((Pi.π (fun b ↦ Over.mk (E.f (i b))) a).left ≫ Sigma.ι E.X (i a)) (by
        show ((Pi.π (fun b ↦ Over.mk (E.f (i b))) a).left ≫
          Sigma.ι E.X (i a)) ≫ Sigma.desc E.f = Q.hom ≫ 𝟙 T
        rw [Category.assoc, Sigma.ι_desc, Category.comp_id]
        exact Over.w (Pi.π (fun b ↦ Over.mk (E.f (i b))) a)))
  show m.left = _
  have hm : e.inv ≫ m = Limits.Pi.map (fun a ↦ (coproductOverCofan E).inj (i a)) := by
    apply Pi.hom_ext
    intro a
    dsimp [m]
    simp only [Category.assoc, Pi.lift_π]
    apply Over.OverMorphism.ext
    simp [e, coproductOverCofan, Cofan.inj]
  simpa [Over.comp_left, e] using congrArg (fun f ↦ f.left) hm

-- The degree-`n` object of a Čech complex is the product that `Pi.hom_ext` presents only after
-- unfolding the chain of plain `def`s building the complex from the simplicial formal
-- coproduct, starting with `Limits.FormalCoproduct.evalOp`. Without that unfolding at
-- `implicit` transparency the associativity move below cannot see the two sides as composable.
attribute [local implicit_reducible] cechFormalCoproduct
  CategoryTheory.Limits.FormalCoproduct.evalOp
  CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
  CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor
  AlgebraicTopology.alternatingCofaceMapComplex
  AlgebraicTopology.AlternatingCofaceMapComplex.obj
  CategoryTheory.PreZeroHypercover.singleton in
/-- On a finitary extensive category, a presheaf preserving finite products has the same Čech
complex for a finite family of morphisms with fixed target as for the single morphism from the
coproduct of that family. -/
theorem isIso_cechComplexMap_of_preservesFiniteProducts [FinitaryExtensive C]
    {T : C} (E : PreZeroHypercover.{w} T) [Finite E.I₀]
    {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
    (F : Cᵒᵖ ⥤ A) [PreservesFiniteProducts F] :
    IsIso (cechComplexMap E
      (PreZeroHypercover.singleton.{w} (Sigma.desc E.f)) (coproductRefinement E) F) := by
  have : ∀ n, IsIso ((cechComplexMap E
      (PreZeroHypercover.singleton.{w} (Sigma.desc E.f)) (coproductRefinement E) F).f n) := by
    intro n
    let : FinitaryExtensive (Over T) :=
      finitaryExtensive_of_preserves_and_reflects (Over.forget T)
    have : PreservesFiniteCoproducts (Over.forget T) := ⟨fun _ ↦ inferInstance⟩
    have : PreservesFiniteProducts (Over.forget T).op := preservesFiniteProducts_op _
    let G := (Over.forget T).op ⋙ F
    let c := coproductOverCofan E
    let hc := (nonempty_isColimit_powerCofan c (isColimit_coproductOverCofan E) (n + 1)).some
    let m := Pi.lift (fun i : Fin (n + 1) → E.I₀ ↦
      G.map (Limits.Pi.map (f := fun a ↦ Over.mk (E.f (i a)))
        (g := fun _ : Fin (n + 1) ↦ Over.mk (Sigma.desc E.f))
        (fun a ↦ c.inj (i a))).op)
    have hm : IsIso m := (Fan.nonempty_isLimit_iff_isIso_piLift _).mp
      ⟨isLimitFanMkObjOfIsLimit G _ _ (Cofan.IsColimit.op hc)⟩
    have heq : (cechComplexMap E
        (PreZeroHypercover.singleton.{w} (Sigma.desc E.f)) (coproductRefinement E) F).f n =
        Pi.π (fun j : Fin (n + 1) → PUnit.{w + 1} ↦
          F.obj (Opposite.op ((∏ᶜ (fun a ↦ Over.mk
            ((PreZeroHypercover.singleton.{w} (Sigma.desc E.f)).f (j a)))).left)))
          default ≫ m := by
      apply Pi.hom_ext
      intro i
      refine (cechComplexMap_f_Pi_π E
        (PreZeroHypercover.singleton.{w} (Sigma.desc E.f)) (coproductRefinement E) F n i).trans ?_
      dsimp [m, G, c, cechSimplicialObject, cechFormalCoproduct]
      rw [Category.assoc, Pi.lift_π, cechProductMap_coproduct]
      rfl
    rw [heq]
    have : IsIso (Pi.π (fun j : Fin (n + 1) → PUnit.{w + 1} ↦
        F.obj (Opposite.op ((∏ᶜ (fun a ↦ Over.mk
          ((PreZeroHypercover.singleton.{w} (Sigma.desc E.f)).f (j a)))).left))) default) := by
      rw [← productUniqueIso_hom]
      infer_instance
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end CechComparison

end Stacks.CechSite

/-! ### Supplementary declarations -/

@[expose] public section
namespace Stacks.CechSite
open CategoryTheory CategoryTheory.Limits
section
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
attribute [local implicit_reducible] Fin.cases Fin.induction Fin.induction.go in
/-- **The `n`-fold power of a coproduct is the coproduct, indexed by `n`-tuples of indices, of
the corresponding products of the summands**, as soon as the coproducts involved are universal.

Universality is asked for as a hypothesis rather than through `FinitaryPreExtensive`, because
the statement is needed both for a finite index type — where a finitary pre-extensive category
supplies it — and for an arbitrary one, where it is the infinitary extensivity of the site, and
only the two index types `I` and `Fin m → I` ever occur. This generalizes
`nonempty_isColimit_powerCofan`, which asks for a finite index type and `FinitaryPreExtensive`. -/
private theorem nonempty_isColimit_powerCofan'
    {I : Type w} {X : I → C} (c : Cofan X) (hc : IsColimit c)
    (hu : ∀ {D : Discrete I ⥤ C} {d : Cocone D}, IsColimit d → IsUniversalColimit d)
    (hu' : ∀ {m : ℕ} {D : Discrete (Fin m → I) ⥤ C} {d : Cocone D},
      IsColimit d → IsUniversalColimit d)
    (n : ℕ) :
    Nonempty (IsColimit (Cofan.mk (∏ᶜ (fun _ : Fin n ↦ c.pt))
      (fun i : Fin n → I ↦ Limits.Pi.map (f := fun a ↦ X (i a))
        (g := fun _ ↦ c.pt) (fun a ↦ c.inj (i a))))) := by
  induction n with
  | zero =>
    let e (i : Fin 0 → I) : (∏ᶜ (fun a ↦ X (i a))) ≅ ∏ᶜ (fun _ : Fin 0 ↦ c.pt) :=
      { hom := Limits.Pi.map (f := fun a ↦ X (i a)) (g := fun _ ↦ c.pt) (fun a ↦ c.inj (i a))
        inv := Pi.lift (fun a ↦ Fin.elim0 a)
        hom_inv_id := Pi.hom_ext _ _ fun a ↦ a.elim0
        inv_hom_id := Pi.hom_ext _ _ fun a ↦ a.elim0 }
    refine ⟨Cofan.IsColimit.mk _ (fun s ↦ (e default).inv ≫ s.inj default) ?_ ?_⟩
    · intro s i
      obtain rfl : i = default := Subsingleton.elim _ _
      show (e default).hom ≫ (e default).inv ≫ s.inj default = _
      simp
    · intro s m hm
      have h := hm default
      change (e default).hom ≫ m = s.inj default at h
      simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using
        congrArg (fun k ↦ (e default).inv ≫ k) h
  | succ n ih =>
    let d := Cofan.mk (∏ᶜ (fun _ : Fin n ↦ c.pt))
      (fun i : Fin n → I ↦ Limits.Pi.map (f := fun a ↦ X (i a))
        (g := fun _ ↦ c.pt) (fun a ↦ c.inj (i a)))
    let e : I × (Fin n → I) ≃ (Fin (n + 1) → I) :=
      { toFun p := Fin.cases p.1 p.2
        invFun i := (i 0, fun a ↦ i a.succ)
        left_inv p := rfl
        right_inv i := by
          funext a
          induction a using Fin.cases <;> rfl }
    let k := Cofan.mk (∏ᶜ (fun _ : Fin (n + 1) ↦ c.pt))
      (fun i : Fin (n + 1) → I ↦ Limits.Pi.map (f := fun a ↦ X (i a))
        (g := fun _ ↦ c.pt) (fun a ↦ c.inj (i a)))
    apply ((Cofan.isColimitEquivOfEquiv e k).symm).nonempty_congr.mp
    refine IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone (hu hc) (hu' ih.some)
      (fun i ↦ terminal.from (X i)) (fun i : Fin n → I ↦ terminal.from (∏ᶜ (fun a ↦ X (i a))))
      (terminal.from c.pt) (terminal.from d.pt)
      (fun i j ↦ (PullbackCone.mk (Pi.π (fun a ↦ X (e (i, j) a)) 0)
        (productTailProjection (fun a ↦ X (e (i, j) a))) (Subsingleton.elim _ _)))
      (fun i j ↦ isLimit_splitProduct (fun a ↦ X (e (i, j) a)))
      (PullbackCone.mk (Pi.π (fun _ : Fin (n + 1) ↦ c.pt) 0)
        (productTailProjection (fun _ : Fin (n + 1) ↦ c.pt)) (Subsingleton.elim _ _))
      (isLimit_splitProduct (fun _ : Fin (n + 1) ↦ c.pt)) (Iso.refl _) ?_ ?_ ?_ ?_
    · intro i
      exact Subsingleton.elim _ _
    · intro i
      exact Subsingleton.elim _ _
    · intro i j
      simp [k, Cofan.inj, PullbackCone.fst, PullbackCone.mk]
      rfl
    · intro i j
      apply Pi.hom_ext
      intro a
      dsimp [k, d, Cofan.inj, PullbackCone.snd, PullbackCone.mk, productTailProjection]
      simp only [Category.id_comp, Category.assoc, Pi.map_π, Pi.lift_π]
      rw [Pi.lift_π_assoc (f := fun b : Fin n ↦ X (j b))]
      rfl

attribute [local implicit_reducible] coproductOverCofan
attribute [local implicit_reducible] cechFormalCoproduct
  CategoryTheory.Limits.FormalCoproduct.evalOp
  CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
  CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor
  AlgebraicTopology.alternatingCofaceMapComplex
  AlgebraicTopology.AlternatingCofaceMapComplex.obj
  CategoryTheory.PreZeroHypercover.singleton in
/-- **The Čech complex of a family agrees with the Čech complex of the morphism from the
coproduct of its members**, as soon as the coproducts in the slice over the common target are
universal and the coefficient presheaf turns the coproducts involved into products.

The two universality hypotheses and the product-preservation are taken as arguments because the
statement is needed both for a finite family on a finitary extensive category and for an
arbitrary family on an infinitary one; see
`Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts` and
`Stacks.CechSite.isIso_cechComplexMap_of_preservesProducts`. -/
private theorem isIso_cechComplexMap_aux
    {T : C} (E : PreZeroHypercover.{w} T) [HasCoproduct E.X]
    {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
    (F : Cᵒᵖ ⥤ A)
    (hu : ∀ {D : Discrete E.I₀ ⥤ Over T} {d : Cocone D}, IsColimit d → IsUniversalColimit d)
    (hu' : ∀ {m : ℕ} {D : Discrete (Fin m → E.I₀) ⥤ Over T} {d : Cocone D},
      IsColimit d → IsUniversalColimit d)
    (hforget : ∀ m : ℕ, PreservesColimitsOfShape
      (Discrete (Fin m → E.I₀)) (Over.forget T))
    (hF : ∀ m : ℕ, PreservesLimitsOfShape (Discrete (Fin m → E.I₀)) F) :
    IsIso (cechComplexMap E
      (PreZeroHypercover.singleton.{w} (Sigma.desc E.f)) (coproductRefinement E) F) := by
  have : ∀ n, IsIso ((cechComplexMap E
      (PreZeroHypercover.singleton.{w} (Sigma.desc E.f)) (coproductRefinement E) F).f n) := by
    intro n
    have := hforget (n + 1)
    have := hF (n + 1)
    have : PreservesLimitsOfShape (Discrete (Fin (n + 1) → E.I₀)) (Over.forget T).op :=
      have : PreservesColimitsOfShape (Discrete (Fin (n + 1) → E.I₀))ᵒᵖ (Over.forget T) :=
        preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _
      preservesLimitsOfShape_op _ _
    let G := (Over.forget T).op ⋙ F
    let c := coproductOverCofan E
    let hc := (nonempty_isColimit_powerCofan' c (isColimit_coproductOverCofan E) hu hu'
      (n + 1)).some
    let m := Pi.lift (fun i : Fin (n + 1) → E.I₀ ↦
      G.map (Limits.Pi.map (f := fun a ↦ Over.mk (E.f (i a)))
        (g := fun _ : Fin (n + 1) ↦ Over.mk (Sigma.desc E.f))
        (fun a ↦ c.inj (i a))).op)
    have hm : IsIso m := (Fan.nonempty_isLimit_iff_isIso_piLift _).mp
      ⟨isLimitFanMkObjOfIsLimit G _ _ (Cofan.IsColimit.op hc)⟩
    have heq : (cechComplexMap E
        (PreZeroHypercover.singleton.{w} (Sigma.desc E.f)) (coproductRefinement E) F).f n =
        Pi.π (fun j : Fin (n + 1) → PUnit.{w + 1} ↦
          F.obj (Opposite.op ((∏ᶜ (fun a ↦ Over.mk
            ((PreZeroHypercover.singleton.{w} (Sigma.desc E.f)).f (j a)))).left)))
          default ≫ m := by
      apply Pi.hom_ext
      intro i
      refine (cechComplexMap_f_Pi_π E
        (PreZeroHypercover.singleton.{w} (Sigma.desc E.f)) (coproductRefinement E) F n i).trans ?_
      dsimp [m, G, c, cechSimplicialObject, cechFormalCoproduct]
      rw [Category.assoc, Pi.lift_π, cechProductMap_coproduct]
      rfl
    rw [heq]
    have : IsIso (Pi.π (fun j : Fin (n + 1) → PUnit.{w + 1} ↦
        F.obj (Opposite.op ((∏ᶜ (fun a ↦ Over.mk
          ((PreZeroHypercover.singleton.{w} (Sigma.desc E.f)).f (j a)))).left))) default) := by
      rw [← productUniqueIso_hom]
      infer_instance
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end
end Stacks.CechSite
end

@[expose] public section
namespace Stacks.CechSite
open CategoryTheory CategoryTheory.Limits
section
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
attribute [local implicit_reducible] coproductOverCofan
/-- **The infinitary comparison.** On a category whose `w`-indexed coproducts are universal, a
presheaf turning `w`-indexed coproducts into products has the same Čech complex for an arbitrary
family of morphisms with fixed target as for the single morphism from the coproduct of that
family.

This is the form the comparison has to take when the family is not assumed finite: the
coefficient presheaf must turn *arbitrary* coproducts into products, which for a sheaf is the
sheaf condition for the covering of a disjoint union by its parts, and the ambient category must
have universal coproducts of arbitrary size. -/
theorem isIso_cechComplexMap_of_preservesProducts
    (huniv : ∀ {I : Type w} {D : Discrete I ⥤ C} {d : Cocone D},
      IsColimit d → IsUniversalColimit d)
    {T : C} (E : PreZeroHypercover.{w} T) [HasCoproducts.{w} C]
    {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
    (F : Cᵒᵖ ⥤ A) [∀ I : Type w, PreservesLimitsOfShape (Discrete I) F] :
    IsIso (cechComplexMap E
      (PreZeroHypercover.singleton.{w} (Sigma.desc E.f)) (coproductRefinement E) F) := by
  have hover : ∀ {I : Type w} {D : Discrete I ⥤ Over T} {d : Cocone D},
      IsColimit d → IsUniversalColimit d := fun {_ _ _} hd ↦
    IsUniversalColimit.of_mapCocone (Over.forget T)
      (huniv (isColimitOfPreserves (Over.forget T) hd))
  exact isIso_cechComplexMap_aux E F hover (fun hd ↦ hover hd)
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)

end
end Stacks.CechSite
end
