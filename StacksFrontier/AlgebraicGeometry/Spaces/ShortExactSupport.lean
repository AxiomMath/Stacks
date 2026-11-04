module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# The support of the middle term of a short exact sequence of modules on an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `0 → F₁ → F₂ → F₃ → 0` be a short exact
sequence of `𝒪_X`-modules.  The support of `F₂`, in the sense of Stacks 04KA, is contained in
the union of the supports of `F₁` and `F₃`.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_middle_subset_union`: the support of the middle term
  of a short exact sequence of `𝒪_X`-modules is contained in the union of the supports of the
  outer two.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 04K1](https://stacks.math.columbia.edu/tag/04K1)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- In the category of types, if `left : A ⟶ D` is a kernel of the pair `right, zero : D ⟶ E` and
`A` and `E` are subsingletons, then `D` is a subsingleton. -/
private theorem subsingleton_of_isLimit_fork {A D E : Type w} (left : A ⟶ D)
    (right zero : D ⟶ E) (comm : left ≫ right = left ≫ zero)
    (hlimit : IsLimit (Fork.ofι left comm)) (hA : Subsingleton A) (hE : Subsingleton E) :
    Subsingleton D := by
  have hfac := hlimit.fac (Fork.ofι (𝟙 D) (by ext; exact hE.elim _ _) : Fork right zero) .zero
  exact ⟨fun a b => (congrArg (· a) hfac).symm.trans
    ((congrArg left (hA.elim _ _)).trans (congrArg (· b) hfac))⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The support of the middle term of a short exact sequence of `𝒪_X`-modules is contained in
the union of the supports of the outer two.** -/
theorem supportOfSheaf_middle_subset_union (X : AlgebraicSpaces B S hS)
    (E : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) (hE : E.ShortExact) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj E.X₂) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj E.X₁) ∪
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj E.X₃) := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := SheafOfModules.instAbelian _
  intro x hx
  by_contra hnot
  simp only [Set.mem_union, not_or] at hnot
  obtain ⟨p, hp, hnon⟩ := hx
  have h1 : Subsingleton (stalkSet p (E.X₁.val.presheaf ⋙ forget AddCommGrpCat.{u})) :=
    not_not.1 fun hs => hnot.1 ⟨p, hp, hs⟩
  have h3 : Subsingleton (stalkSet p (E.X₃.val.presheaf ⋙ forget AddCommGrpCat.{u})) :=
    not_not.1 fun hs => hnot.2 ⟨p, hp, hs⟩
  refine hnon ?_
  have _ := preservesFiniteLimits_moduleStalkSetFunctor.{u, u} B S hS X p
  set T := moduleStalkSetFunctor.{u, u} B S hS X p
  have hcomm : E.f ≫ E.g = E.f ≫ (0 : E.X₂ ⟶ E.X₃) := by rw [E.zero]; simp
  have hfork : IsLimit (Fork.ofι (f := T.map E.g) (g := T.map (0 : E.X₂ ⟶ E.X₃))
      (ι := T.map E.f) (by simpa only [Functor.map_comp] using congrArg T.map hcomm)) :=
    isLimitForkMapOfIsLimit T hcomm hE.fIsKernel
  exact subsingleton_of_isLimit_fork _ _ _ _ hfork h1 h3

end AlgebraicGeometry.Space

end
