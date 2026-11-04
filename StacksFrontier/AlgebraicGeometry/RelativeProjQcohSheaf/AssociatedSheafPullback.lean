module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback

/-!
# The module of Tag 01O6 is compatible with the pullback of a quadruple

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra and `ℳ` a graded `𝒜`-module (Situation 01NN).
Tag 01O6 attaches to a quadruple `(d, f : T → S, L, ψ)` over a test scheme `T` the `𝒪_T`-module

`ℳ̃_T = (f^*ℳ^{(d)} ⊗_{f^*𝒜^{(d)}} (⨁_{n ∈ ℤ} L^{⊗ n}))₀`,

and `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.pullback` carries a quadruple over
`T` to one over a test scheme `T'` along a morphism `g : T' ⟶ T`. This file proves that the two
constructions commute: **`g^*ℳ̃_T` is the module of the pulled-back quadruple.**

The comparison is pinned down by what it does to the degreewise pure tensors, so it is canonical
and not a choice: a morphism out of `ℳ̃_{T'}` is a balanced family of morphisms out of the
degreewise summands, and the condition `associatedSheafPullbackIso_pureTensor` prescribes that
family.

## The construction

`ℳ̃_T` is the cokernel of the balancing relations between the degreewise summands
`f^*ℳ_{nd} ⊗ L^{⊗ (-n)}`. Three canonical comparisons turn the pullback of a summand into the
corresponding summand for `(d, g ∘ f, g^*L, g^*ψ)`: the comparison `g^*(X ⊗ Y) ≅ g^*X ⊗ g^*Y` of
Tag 01CD, the contraction `(g ∘ f)^*X ≅ g^*(f^*X)` of an iterated pullback, and the comparison
`g^*(L^{⊗ i}) ≅ (g^*L)^{⊗ i}` of the integral tensor powers of Tag 01CU. Their composite is
`summandPullback`, and `relationSummandPullback` is its counterpart on the bidegreewise sources
of the relations. The content is that these intertwine the two sides of every balancing
relation, which is `summandPullback_relationLeft` and `summandPullback_relationRight`.

**No exactness of the pullback is used, and the cokernel is never commuted with `g^*`.** What
replaces that is `pullback_existsUnique_hom`: the universal property of `ℳ̃_T` transported along
the adjunction `g^* ⊣ g_*`, which says that a morphism out of `g^*ℳ̃_T` is a balanced family of
morphisms out of the *pullbacks* of the degreewise summands. The forward and backward
comparisons are then built from the two universal properties and are mutually inverse by their
uniqueness halves.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.summandPullback` and `relationSummandPullback`:
  the comparisons of the pullbacks of the degreewise summands and of the bidegreewise sources of
  the balancing relations with their counterparts over `T'`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relationRightInner`: the inner morphism
  `(a, l) ↦ ψ(a) · l` of a balancing relation, isolated so that the associator is the only other
  ingredient of the right-hand side.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.associatedSheafPullbackIso`: **the comparison
  `g^*ℳ̃_T ≅ ℳ̃_{T'}`**, and `Quadruple.associatedSheafPullbackIso` the same read on the pullback
  of a quadruple.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.summandPullback_act`: the contraction of an
  iterated pullback intertwines the actions of `(g ∘ f)^*𝒜^{(d)}` and of `f^*𝒜^{(d)}`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.summandPullback_relationLeft` and
  `summandPullback_relationRight`: **the comparisons intertwine the two sides of every balancing
  relation.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback_mulSheaf`: the comparison of
  the integral tensor powers is multiplicative in the form a balancing relation consumes it, the
  transport to the total degree included.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullback_existsUnique_hom`: **the universal
  property of `ℳ̃_T` transported along `g^* ⊣ g_*`.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.exists_associatedSheafPullbackIso`: **the
  comparison exists and carries the pullback of the degree-`n` pure tensors to the degree-`n`
  pure tensors.**

## Implementation notes

The homogeneous pieces of the Laurent algebra are spelled through
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` while the pullback of sheaves of
modules is spelled through `Stacks.RingedSpace.structureRingSheaf`. The two are equal by `rfl`
and are not syntactically equal, so a goal mentioning both is not type-correct at `implicit`
transparency and `rw` refuses it — reporting a missing pattern rather than the cause. Every
diagram below is therefore reduced to a **rearrangement in an abstract monoidal category**
(`whiskerRight_conj_square`, `whiskerLeft_assoc_conj_square`, `whiskerRight_mul_conj_square`,
`mul_transport_square`), whose objects and morphisms are free variables, and applied with
`exact`, where the defeq is checked at default transparency and the crossing is harmless. The
coherences fed to them — the associator and the two naturalities of Tag 01CD's comparison, the
compatibility of the contraction with that comparison, and the multiplicativity of the
tensor-power comparison — are consumed unchanged.

## Not done here

No Stacks tag is carried. Tag 01O6 asserts the *existence* of `ℳ̃_T`, which
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.associatedSheaf` already carries, and
says nothing about base change. The base-change isomorphism is what the compatibility with
pullback of the comparisons `ℳ̃_T ≅ h^*ℳ̃` of property (1) of Tag 01O7 is stated through: on a
chart datum it is
`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso_pullback`, and for an
arbitrary quadruple and an arbitrary `g : T' ⟶ T` it is
`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.Quadruple.tildeComparison_pullback`.

## References

* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesAbelian
  Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesHasCoproducts

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

section Monoidal

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- A rearrangement in a monoidal category: a square comparing a whiskered morphism with a
conjugate of it, with the two factors of the whiskering compared separately. Both sides are
read as tensor products of morphisms and the first factors are identified by `hact`, the
second by the unit laws. -/
private theorem whiskerRight_conj_square {W V PXY PZ PLp HXY HZ LLp : C} {m : W ⟶ V}
    {eV : V ⟶ PZ ⊗ PLp} {eW : W ⟶ PXY ⊗ PLp} {α : PXY ⟶ PZ} {c : PZ ⟶ HZ} {lp : PLp ⟶ LLp}
    {q : PXY ⟶ HXY} {actH : HXY ⟶ HZ}
    (hnat : m ≫ eV = eW ≫ (α ▷ PLp)) (hact : q ≫ actH = α ≫ c) :
    m ≫ eV ≫ (c ⊗ₘ lp) = (eW ≫ (q ⊗ₘ lp)) ≫ (actH ▷ LLp) := by
  rw [← Category.assoc, hnat, Category.assoc, Category.assoc,
    ← MonoidalCategory.tensorHom_id α, ← MonoidalCategory.tensorHom_id actH,
    MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, hact]

/-- A rearrangement in a monoidal category: the square for a morphism whiskered on the *left*,
with the associator inserted on both sides. -/
private theorem whiskerLeft_assoc_conj_square {W V₁ V₂ a b e p pab f₁ A' B' E' F' : C}
    {mfull : W ⟶ V₂}
    {mα : W ⟶ V₁} {mw : V₁ ⟶ V₂} {e₁ : V₁ ⟶ a ⊗ p} {e₂ : V₂ ⟶ a ⊗ f₁} {eBE : p ⟶ b ⊗ e}
    {eW : W ⟶ pab ⊗ e} {eAB : pab ⟶ a ⊗ b} {pw : p ⟶ f₁} {cM : a ⟶ A'} {cA : b ⟶ B'}
    {lp : e ⟶ E'} {lp₁ : f₁ ⟶ F'} {w : B' ⊗ E' ⟶ F'} (hm : mfull = mα ≫ mw)
    (hassoc : mα ≫ e₁ ≫ (a ◁ eBE) = eW ≫ (eAB ▷ e) ≫ (α_ a b e).hom)
    (hnat : mw ≫ e₂ = e₁ ≫ (a ◁ pw)) (hw : eBE ≫ (cA ⊗ₘ lp) ≫ w = pw ≫ lp₁) :
    mfull ≫ e₂ ≫ (cM ⊗ₘ lp₁) =
      (eW ≫ ((eAB ≫ (cM ⊗ₘ cA)) ⊗ₘ lp)) ≫ (α_ A' B' E').hom ≫ (A' ◁ w) := by
  subst hm
  rw [Category.assoc]
  have h₁ : (a ◁ pw) ≫ (cM ⊗ₘ lp₁) = (a ◁ eBE) ≫ (cM ⊗ₘ ((cA ⊗ₘ lp) ≫ w)) := by
    rw [← MonoidalCategory.id_tensorHom a pw, ← MonoidalCategory.id_tensorHom a eBE,
      MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom, hw]
  have h₂ : (eAB ≫ (cM ⊗ₘ cA)) ⊗ₘ lp = (eAB ▷ e) ≫ ((cM ⊗ₘ cA) ⊗ₘ lp) := by
    rw [← MonoidalCategory.tensorHom_id eAB e, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.id_comp]
  have h₃ : (cM ⊗ₘ (cA ⊗ₘ lp)) ≫ (A' ◁ w) = cM ⊗ₘ ((cA ⊗ₘ lp) ≫ w) := by
    rw [← MonoidalCategory.id_tensorHom A' w, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id]
  calc mα ≫ mw ≫ e₂ ≫ (cM ⊗ₘ lp₁)
      = mα ≫ (mw ≫ e₂) ≫ (cM ⊗ₘ lp₁) := by simp only [Category.assoc]
    _ = (mα ≫ e₁ ≫ (a ◁ eBE)) ≫ (cM ⊗ₘ ((cA ⊗ₘ lp) ≫ w)) := by
          rw [hnat]
          simp only [Category.assoc]
          rw [h₁]
    _ = (eW ≫ (eAB ▷ e) ≫ (α_ a b e).hom) ≫ (cM ⊗ₘ ((cA ⊗ₘ lp) ≫ w)) := by rw [hassoc]
    _ = (eW ≫ ((eAB ≫ (cM ⊗ₘ cA)) ⊗ₘ lp)) ≫ (α_ A' B' E').hom ≫ (A' ◁ w) := by
          rw [h₂]
          simp only [Category.assoc]
          rw [MonoidalCategory.associator_naturality_assoc, h₃]

/-- A rearrangement in a monoidal category: the square for the inner morphism `ψ(a) · l` of a
balancing relation, with the comparison of the first factor supplied by `hpsi` and that of the
multiplication by `hmul`. -/
private theorem whiskerRight_mul_conj_square {WY W Z pY pLi pLj HY L'i L'j F' : C}
    {eY : WY ⟶ pY ⊗ pLj} {e : W ⟶ pLi ⊗ pLj} {m : WY ⟶ W} {pψ : pY ⟶ pLi} {cA : pY ⟶ HY}
    {lpi : pLi ⟶ L'i} {lpj : pLj ⟶ L'j} {ψ' : HY ⟶ L'i} {rest : L'i ⊗ L'j ⟶ F'} {r : W ⟶ Z}
    {lpk : Z ⟶ F'} {mi : WY ⟶ Z}
    (hnat : m ≫ e = eY ≫ (pψ ▷ pLj)) (hpsi : cA ≫ ψ' = pψ ≫ lpi)
    (hmul : e ≫ (lpi ⊗ₘ lpj) ≫ rest = r ≫ lpk) (hcomp : m ≫ r = mi) :
    eY ≫ (cA ⊗ₘ lpj) ≫ ((ψ' ▷ L'j) ≫ rest) = mi ≫ lpk := by
  have h₁ : (cA ⊗ₘ lpj) ≫ (ψ' ▷ L'j) = (pψ ▷ pLj) ≫ (lpi ⊗ₘ lpj) := by
    rw [← MonoidalCategory.tensorHom_id ψ' L'j, ← MonoidalCategory.tensorHom_id pψ pLj,
      MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, hpsi]
  calc eY ≫ (cA ⊗ₘ lpj) ≫ ((ψ' ▷ L'j) ≫ rest)
      = eY ≫ ((cA ⊗ₘ lpj) ≫ (ψ' ▷ L'j)) ≫ rest := by simp only [Category.assoc]
    _ = (eY ≫ (pψ ▷ pLj)) ≫ (lpi ⊗ₘ lpj) ≫ rest := by rw [h₁]; simp only [Category.assoc]
    _ = m ≫ e ≫ (lpi ⊗ₘ lpj) ≫ rest := by rw [← hnat]; simp only [Category.assoc]
    _ = mi ≫ lpk := by rw [hmul, ← Category.assoc, hcomp]

omit [MonoidalCategory C] in
/-- A rearrangement: a comparison square for a composite whose second factor is itself a
composite of a multiplication and a transport along an equality of degrees. -/
private theorem mul_transport_square {W X Y V V' U F : C} {e : W ⟶ X} {t : X ⟶ Y} {m : Y ⟶ V'}
    {et : V' ⟶ F} {pm : W ⟶ V} {lp : V ⟶ V'} {pet : V ⟶ U} {lpk : U ⟶ F} {pmi : W ⟶ U}
    (hmul : e ≫ t ≫ m = pm ≫ lp) (heq : lp ≫ et = pet ≫ lpk) (hcomp : pm ≫ pet = pmi) :
    e ≫ t ≫ (m ≫ et) = pmi ≫ lpk := by
  subst hcomp
  calc e ≫ t ≫ (m ≫ et) = (e ≫ t ≫ m) ≫ et := by simp only [Category.assoc]
    _ = pm ≫ lp ≫ et := by rw [hmul, Category.assoc]
    _ = (pm ≫ pet) ≫ lpk := by rw [heq, Category.assoc]

end Monoidal

variable {T' T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
  (M : SheafOfModules.GradedModule.{u, u, u} A) (d : ℤ)
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (g : T' ⟶ T)

/-- The comparison `g^*(f^*ℳ_{nd} ⊗ L^{⊗ (-n)}) ⟶ (g ∘ f)^*ℳ_{nd} ⊗ (g^*L)^{⊗ (-n)}`. -/
def summandPullback (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom g)).obj (summand f M d L n) ⟶
      summand (g ≫ f) M d ((pullbackFunctor (ringedSpaceHom g)).obj L) n :=
  pullbackTensorComparison (ringedSpaceHom g)
      ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (n * d))) ((laurent L).piece (-n)) ≫
    (inv (compComparison g f (M.piece (n * d))) ⊗ₘ laurentPullback g L (-n))

/-- The contraction of an iterated pullback carries the action of `(g ∘ f)^*𝒜^{(d)}` to the
pullback of the action of `f^*𝒜^{(d)}`. -/
theorem summandPullback_act (n i : ℤ) :
    pullbackTensorComparison (ringedSpaceHom g)
          ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (n * d)))
          ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d))) ≫
        (inv (compComparison g f (M.piece (n * d))) ⊗ₘ
          inv (compComparison g f (A.piece (i * d)))) ≫
          act (g ≫ f) M d n i ≫ compComparison g f (M.piece ((n + i) * d)) =
      (pullbackFunctor (ringedSpaceHom g)).map (act f M d n i) := by
  set μ : M.piece (n * d) ⊗ A.piece (i * d) ⟶ M.piece ((n + i) * d) :=
    M.smulSheaf (n * d) (i * d) ≫
      eqToHom (congrArg M.piece (by ring : n * d + i * d = (n + i) * d)) with hμ
  have hnat := compComparison_naturality g f μ
  have key : pullbackTensorComparison (ringedSpaceHom g)
          ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (n * d)))
          ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d))) ≫
        (inv (compComparison g f (M.piece (n * d))) ⊗ₘ
          inv (compComparison g f (A.piece (i * d)))) ≫
          inv (pullbackTensorComparison (ringedSpaceHom (g ≫ f)) (M.piece (n * d))
            (A.piece (i * d))) ≫
            compComparison g f (M.piece (n * d) ⊗ A.piece (i * d)) =
      inv ((pullbackFunctor (ringedSpaceHom g)).map
        (pullbackTensorComparison (ringedSpaceHom f) (M.piece (n * d)) (A.piece (i * d)))) := by
    rw [inv_pullbackTensorComparison_comp_compComparison]
    simp
  have hacth : act (g ≫ f) M d n i =
      inv (pullbackTensorComparison (ringedSpaceHom (g ≫ f)) (M.piece (n * d))
        (A.piece (i * d))) ≫ (pullbackFunctor (ringedSpaceHom (g ≫ f))).map μ := rfl
  have hactf : act f M d n i =
      inv (pullbackTensorComparison (ringedSpaceHom f) (M.piece (n * d))
        (A.piece (i * d))) ≫ (pullbackFunctor (ringedSpaceHom f)).map μ := rfl
  rw [hacth, hactf, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv]
  simp only [Category.assoc]
  rw [← hnat, ← key]
  simp only [Category.assoc]

/-- The comparison
`g^*((f^*ℳ_{nd} ⊗ f^*𝒜_{id}) ⊗ L^{⊗ (-(n+i))}) ⟶ ((g ∘ f)^*ℳ_{nd} ⊗ (g ∘ f)^*𝒜_{id}) ⊗
(g^*L)^{⊗ (-(n+i))}`. -/
def relationSummandPullback (p : ℤ × ℤ) :
    (pullbackFunctor (ringedSpaceHom g)).obj (relationSummand f M d L p) ⟶
      relationSummand (g ≫ f) M d ((pullbackFunctor (ringedSpaceHom g)).obj L) p :=
  pullbackTensorComparison (ringedSpaceHom g)
      ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)) ⊗
        (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d)))
      ((laurent L).piece (-(p.1 + p.2))) ≫
    ((pullbackTensorComparison (ringedSpaceHom g)
          ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)))
          ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d))) ≫
        (inv (compComparison g f (M.piece (p.1 * d))) ⊗ₘ
          inv (compComparison g f (A.piece (p.2 * d))))) ⊗ₘ
      laurentPullback g L (-(p.1 + p.2)))

/-- The comparisons carry the pullback of a balancing relation's left-hand side to the
left-hand side of the pulled-back relation. -/
theorem summandPullback_relationLeft (p : ℤ × ℤ) :
    (pullbackFunctor (ringedSpaceHom g)).map (relationLeft f M d L p) ≫
        summandPullback M d L g (p.1 + p.2) =
      relationSummandPullback M d L g p ≫
        relationLeft (g ≫ f) M d ((pullbackFunctor (ringedSpaceHom g)).obj L) p := by
  have hact : (pullbackTensorComparison (ringedSpaceHom g)
          ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)))
          ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d))) ≫
        (inv (compComparison g f (M.piece (p.1 * d))) ⊗ₘ
          inv (compComparison g f (A.piece (p.2 * d))))) ≫ act (g ≫ f) M d p.1 p.2 =
      (pullbackFunctor (ringedSpaceHom g)).map (act f M d p.1 p.2) ≫
        inv (compComparison g f (M.piece ((p.1 + p.2) * d))) := by
    rw [IsIso.eq_comp_inv]
    simp only [Category.assoc]
    exact summandPullback_act M d g p.1 p.2
  exact whiskerRight_conj_square
    (pullbackTensorComparison_naturality_left (f := ringedSpaceHom g)
      (B := (laurent L).piece (-(p.1 + p.2))) (act f M d p.1 p.2)) hact

/-- The comparison of the integral tensor powers commutes with a transport along an equality of
degrees. -/
theorem laurentPullback_eqToHom {i j : ℤ} (h : i = j) :
    laurentPullback g L i ≫
        eqToHom (congrArg (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).piece h) =
      (pullbackFunctor (ringedSpaceHom g)).map (eqToHom (congrArg (laurent L).piece h)) ≫
        laurentPullback g L j := by
  subst h
  simp only [eqToHom_refl, Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The comparison of the integral tensor powers is multiplicative**, in the form in which a
balancing relation of Tag 01O6 consumes it: the multiplication of the Laurent algebra followed by
the transport to the total degree. -/
theorem laurentPullback_mulSheaf (i j k : ℤ) (h : i + j = k) :
    pullbackTensorComparison (ringedSpaceHom g) ((laurent L).piece i) ((laurent L).piece j) ≫
        (laurentPullback g L i ⊗ₘ laurentPullback g L j) ≫
          ((laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).mulSheaf i j ≫
            eqToHom (congrArg
              (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).piece h)) =
      (pullbackFunctor (ringedSpaceHom g)).map
          ((laurent L).mulSheaf i j ≫ eqToHom (congrArg (laurent L).piece h)) ≫
        laurentPullback g L k := by
  rw [laurent_mulSheaf_eq L i j,
    laurent_mulSheaf_eq ((pullbackFunctor (ringedSpaceHom g)).obj L) i j]
  exact mul_transport_square (laurentPullback_mul g L i j) (laurentPullback_eqToHom L g h)
    ((pullbackFunctor (ringedSpaceHom g)).map_comp _ _).symm

variable {M d L}

/-- The inner morphism `(a, l) ↦ ψ(a) · l` of a balancing relation of Tag 01O6, in bidegree
`(n, i)`: the value of `ψ` on the algebra factor, multiplied into the Laurent algebra. -/
def relationRightInner (ψ : Twisting f A d L) (p : ℤ × ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d)) ⊗
        (laurent L).piece (-(p.1 + p.2)) ⟶ (laurent L).piece (-p.1) :=
  (ψ.app p.2 ▷ (laurent L).piece (-(p.1 + p.2))) ≫
    (laurent L).mulSheaf p.2 (-(p.1 + p.2)) ≫
      eqToHom (congrArg (laurent L).piece (by ring : p.2 + -(p.1 + p.2) = -p.1))

/-- The right-hand side of a balancing relation is the associator followed by the inner
morphism whiskered into the module factor. -/
theorem relationRight_eq (M : SheafOfModules.GradedModule.{u, u, u} A) (ψ : Twisting f A d L)
    (p : ℤ × ℤ) :
    Twisting.relationRight M ψ p =
      (α_ ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)))
        ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d)))
        ((laurent L).piece (-(p.1 + p.2)))).hom ≫
        ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)) ◁
          relationRightInner ψ p) := rfl

/-- **The comparisons carry the pullback of the inner morphism of a balancing relation to the
inner morphism of the pulled-back relation.** -/
theorem relationRightInner_pullback (ψ : Twisting f A d L) (g : T' ⟶ T) (p : ℤ × ℤ) :
    pullbackTensorComparison (ringedSpaceHom g)
          ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d)))
          ((laurent L).piece (-(p.1 + p.2))) ≫
        (inv (compComparison g f (A.piece (p.2 * d))) ⊗ₘ
            laurentPullback g L (-(p.1 + p.2))) ≫
          relationRightInner (ψ.pullback g) p =
      (pullbackFunctor (ringedSpaceHom g)).map (relationRightInner ψ p) ≫
        laurentPullback g L (-p.1) :=
  whiskerRight_mul_conj_square
    (pullbackTensorComparison_naturality_left (f := ringedSpaceHom g)
      (B := (laurent L).piece (-(p.1 + p.2))) (ψ.app p.2))
    (IsIso.inv_hom_id_assoc _ _)
    (laurentPullback_mulSheaf L g p.2 (-(p.1 + p.2)) (-p.1) (by ring))
    ((pullbackFunctor (ringedSpaceHom g)).map_comp _ _).symm

variable (M d L)

/-- The comparisons carry the pullback of a balancing relation's right-hand side to the
right-hand side of the pulled-back relation. -/
theorem summandPullback_relationRight (ψ : Twisting f A d L) (p : ℤ × ℤ) :
    (pullbackFunctor (ringedSpaceHom g)).map (Twisting.relationRight M ψ p) ≫
        summandPullback M d L g p.1 =
      relationSummandPullback M d L g p ≫
        Twisting.relationRight M (ψ.pullback g) p :=
  whiskerLeft_assoc_conj_square
    ((pullbackFunctor (ringedSpaceHom g)).map_comp
      (α_ ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)))
        ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d)))
        ((laurent L).piece (-(p.1 + p.2)))).hom
      ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)) ◁
        relationRightInner ψ p))
    (pullbackTensorComparison_associator (ringedSpaceHom g)
      ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)))
      ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d)))
      ((laurent L).piece (-(p.1 + p.2))))
    (pullbackTensorComparison_naturality_right (f := ringedSpaceHom g)
      (A := (pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)))
      (relationRightInner ψ p))
    (relationRightInner_pullback ψ g p)

/-- The comparison `summandPullback M d L g n` is an isomorphism. -/
instance isIso_summandPullback (n : ℤ) : IsIso (summandPullback (f := f) M d L g n) :=
  (asIso (pullbackTensorComparison (ringedSpaceHom g)
        ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (n * d))) ((laurent L).piece (-n))) ≪≫
      ((asIso (compComparison g f (M.piece (n * d)))).symm ⊗ᵢ
        asIso (laurentPullback g L (-n)))).isIso_hom

/-- The comparison `relationSummandPullback M d L g p` is an isomorphism. -/
instance isIso_relationSummandPullback (p : ℤ × ℤ) :
    IsIso (relationSummandPullback (f := f) M d L g p) :=
  (asIso (pullbackTensorComparison (ringedSpaceHom g)
        ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)) ⊗
          (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d)))
        ((laurent L).piece (-(p.1 + p.2)))) ≪≫
      ((asIso (pullbackTensorComparison (ringedSpaceHom g)
            ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece (p.1 * d)))
            ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p.2 * d)))) ≪≫
          ((asIso (compComparison g f (M.piece (p.1 * d)))).symm ⊗ᵢ
            (asIso (compComparison g f (A.piece (p.2 * d)))).symm)) ⊗ᵢ
        asIso (laurentPullback g L (-(p.1 + p.2))))).isIso_hom

/-- **The universal property of `ℳ̃_T` transported along the pullback.** A morphism out of
`g^*ℳ̃_T` is the same thing as a balanced family of morphisms out of the pullbacks of the
degreewise pure tensors. The adjunction `g^* ⊣ g_*` carries the one statement to the other, and
no exactness of the pullback is used. -/
theorem pullback_existsUnique_hom (ψ : Twisting f A d L)
    (N : SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace))
    (b : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom g)).obj (summand f M d L n) ⟶ N)
    (hb : ∀ p : ℤ × ℤ,
      (pullbackFunctor (ringedSpaceHom g)).map (relationLeft f M d L p) ≫ b (p.1 + p.2) =
        (pullbackFunctor (ringedSpaceHom g)).map (Twisting.relationRight M ψ p) ≫ b p.1) :
    ∃! h : (pullbackFunctor (ringedSpaceHom g)).obj (Twisting.associatedSheaf M ψ) ⟶ N,
      ∀ n : ℤ,
        (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ n) ≫ h = b n := by
  obtain ⟨k, hk, huniq⟩ := Twisting.existsUnique_hom M ψ
    ((pushforwardFunctor (ringedSpaceHom g)).obj N)
    (fun n => (pullbackAdjunction (ringedSpaceHom g)).homEquiv _ N (b n)) (fun p => by
      rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left, hb p])
  refine ⟨((pullbackAdjunction (ringedSpaceHom g)).homEquiv _ N).symm k, fun n => ?_,
    fun h' hh' => ?_⟩
  · refine ((pullbackAdjunction (ringedSpaceHom g)).homEquiv _ N).injective ?_
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply, hk n]
  · refine ((pullbackAdjunction (ringedSpaceHom g)).homEquiv _ N).injective ?_
    rw [Equiv.apply_symm_apply]
    exact huniq _ fun n => by rw [← Adjunction.homEquiv_naturality_left, hh' n]

/-- The family of comparisons followed by the pure tensors of the pulled-back quadruple is
balanced, read on the pullbacks of the degreewise pure tensors. -/
theorem summandPullback_pureTensor_balanced (ψ : Twisting f A d L) (p : ℤ × ℤ) :
    (pullbackFunctor (ringedSpaceHom g)).map (relationLeft f M d L p) ≫
        summandPullback M d L g (p.1 + p.2) ≫
          Twisting.pureTensor M (ψ.pullback g) (p.1 + p.2) =
      (pullbackFunctor (ringedSpaceHom g)).map (Twisting.relationRight M ψ p) ≫
        summandPullback M d L g p.1 ≫ Twisting.pureTensor M (ψ.pullback g) p.1 := by
  rw [← Category.assoc, summandPullback_relationLeft, Category.assoc,
    Twisting.relationLeft_pureTensor, ← Category.assoc, ← summandPullback_relationRight,
    Category.assoc]

/-- The pullback of the pure tensors of `ℳ̃_T` is balanced for the pullback of the relations. -/
private theorem map_relationLeft_pureTensor (ψ : Twisting f A d L) (p : ℤ × ℤ) :
    (pullbackFunctor (ringedSpaceHom g)).map (relationLeft f M d L p) ≫
        (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ (p.1 + p.2)) =
      (pullbackFunctor (ringedSpaceHom g)).map (Twisting.relationRight M ψ p) ≫
        (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ p.1) := by
  rw [← Functor.map_comp, Twisting.relationLeft_pureTensor, Functor.map_comp]

/-- The family of inverse comparisons followed by the pullbacks of the pure tensors is
balanced for the pulled-back quadruple. -/
theorem summandPullback_inv_pureTensor_balanced (ψ : Twisting f A d L) (p : ℤ × ℤ) :
    relationLeft (g ≫ f) M d ((pullbackFunctor (ringedSpaceHom g)).obj L) p ≫
        inv (summandPullback M d L g (p.1 + p.2)) ≫
          (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ (p.1 + p.2)) =
      Twisting.relationRight M (ψ.pullback g) p ≫ inv (summandPullback M d L g p.1) ≫
        (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ p.1) := by
  have hL : relationLeft (g ≫ f) M d ((pullbackFunctor (ringedSpaceHom g)).obj L) p =
      inv (relationSummandPullback M d L g p) ≫
        (pullbackFunctor (ringedSpaceHom g)).map (relationLeft f M d L p) ≫
          summandPullback M d L g (p.1 + p.2) :=
    (IsIso.eq_inv_comp _).mpr (summandPullback_relationLeft M d L g p).symm
  have hR : Twisting.relationRight M (ψ.pullback g) p =
      inv (relationSummandPullback M d L g p) ≫
        (pullbackFunctor (ringedSpaceHom g)).map (Twisting.relationRight M ψ p) ≫
          summandPullback M d L g p.1 :=
    (IsIso.eq_inv_comp _).mpr (summandPullback_relationRight M d L g ψ p).symm
  rw [hL, hR]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [map_relationLeft_pureTensor M d L g ψ p]

/-- **Stacks Project, Tag 01O6, compatibility with base change.** The module `ℳ̃_T` attached to a
quadruple `(d, f : T → S, L, ψ)` is compatible with the pullback along a morphism `g : T' ⟶ T` of
test schemes: `g^*ℳ̃_T` is the module `ℳ̃_{T'}` of the pulled-back quadruple
`(d, g ∘ f, g^*L, g^*ψ)`, by an isomorphism carrying the pullback of the degree-`n` pure tensors
to the degree-`n` pure tensors. -/
theorem exists_associatedSheafPullbackIso (ψ : Twisting f A d L) :
    ∃ e : (pullbackFunctor (ringedSpaceHom g)).obj (Twisting.associatedSheaf M ψ) ≅
        Twisting.associatedSheaf M (ψ.pullback g),
      ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ n) ≫ e.hom =
        summandPullback M d L g n ≫ Twisting.pureTensor M (ψ.pullback g) n := by
  obtain ⟨φ, hφ, -⟩ := pullback_existsUnique_hom M d L g ψ _
    (fun n => summandPullback M d L g n ≫ Twisting.pureTensor M (ψ.pullback g) n)
    (summandPullback_pureTensor_balanced M d L g ψ)
  obtain ⟨χ, hχ, -⟩ := Twisting.existsUnique_hom M (ψ.pullback g)
    ((pullbackFunctor (ringedSpaceHom g)).obj (Twisting.associatedSheaf M ψ))
    (fun n => inv (summandPullback M d L g n) ≫
      (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ n))
    (summandPullback_inv_pureTensor_balanced M d L g ψ)
  have hu₁ := pullback_existsUnique_hom M d L g ψ _
    (fun n => (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ n))
    (map_relationLeft_pureTensor M d L g ψ)
  have hu₂ := Twisting.existsUnique_hom M (ψ.pullback g)
    (Twisting.associatedSheaf M (ψ.pullback g)) (Twisting.pureTensor M (ψ.pullback g))
    (Twisting.relationLeft_pureTensor M (ψ.pullback g))
  refine ⟨⟨φ, χ, ?_, ?_⟩, hφ⟩
  · refine hu₁.unique (fun n => ?_) (fun _ => Category.comp_id _)
    rw [← Category.assoc, hφ n, Category.assoc, hχ n, IsIso.hom_inv_id_assoc]
  · refine hu₂.unique (fun n => ?_) (fun _ => Category.comp_id _)
    rw [← Category.assoc, hχ n, Category.assoc, hφ n, IsIso.inv_hom_id_assoc]

/-- **`g^*ℳ̃_T ≅ ℳ̃_{T'}` for the pulled-back quadruple.** The module of Tag 01O6 attached to a
quadruple `(d, f : T → S, L, ψ)` is compatible with the pullback along a morphism `g : T' ⟶ T` of
test schemes. It is pinned down by `associatedSheafPullbackIso_pureTensor`, which says that it
carries the pullback of the degree-`n` pure tensors to the degree-`n` pure tensors of the
pulled-back quadruple; by the universal property `Twisting.existsUnique_hom` that condition
determines the forward morphism, and hence the isomorphism, uniquely. -/
def associatedSheafPullbackIso (ψ : Twisting f A d L) :
    (pullbackFunctor (ringedSpaceHom g)).obj (Twisting.associatedSheaf M ψ) ≅
      Twisting.associatedSheaf M (ψ.pullback g) :=
  (exists_associatedSheafPullbackIso M d L g ψ).choose

/-- The comparison carries the pullback of the degree-`n` pure tensors of `ℳ̃_T` to the
degree-`n` pure tensors of `ℳ̃_{T'}`, read through the comparison of the degreewise summands. -/
theorem associatedSheafPullbackIso_pureTensor (ψ : Twisting f A d L) (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ n) ≫
        (associatedSheafPullbackIso M d L g ψ).hom =
      summandPullback M d L g n ≫ Twisting.pureTensor M (ψ.pullback g) n :=
  (exists_associatedSheafPullbackIso M d L g ψ).choose_spec n

/-- **The module of Tag 01O6 of a quadruple is compatible with the pullback of the quadruple.**
This is `associatedSheafPullbackIso` read on `Quadruple.pullback`, which is the form in which
property (1) of Tag 01O7 consumes it: the quadruple over `T'` whose classifying morphism is
`g ≫ h` is `P.pullback g`, and its module is the pullback of the module of `P`. -/
def Quadruple.associatedSheafPullbackIso (M : SheafOfModules.GradedModule.{u, u, u} A)
    (P : Quadruple f A d) (g : T' ⟶ T) :
    (pullbackFunctor (ringedSpaceHom g)).obj (Twisting.associatedSheaf M P.twisting) ≅
      Twisting.associatedSheaf M (P.pullback g).twisting :=
  _root_.Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.associatedSheafPullbackIso M d P.L g
    P.twisting

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
