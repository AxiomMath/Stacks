module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackConstantData
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorStackUnconditional
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FullyFaithfulEquivalence
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageLeftEqualizer

/-!
# The quotient by an abstract group is the quotient by the constant group (Stacks 0371)

Let `S` be a scheme of a big fppf site, `G` an abstract group whose constant group scheme `G_S`
lies in the site (the cardinality bound of the source), `X` an algebraic space over `S` and
`ρ : G →* Aut X` an action. The last clause of Stacks 0371 asserts that the stack `[[X/G]]` of
triples `(U, P, φ)` with `P` a torsor under the constant sheaf `G` is equivalent to the stack
`[[X/G_S]]` of Situation 04WL. This file proves it.

The comparison functor `[[X/G_S]] ⥤ [[X/G]]` is
`AlgebraicGeometry.Space.torsorWithMapToAbstractQuotient`, fed with the data of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackConstantData`. It is
fully faithful, both sides are stacks (Stacks 0370 and the first clause of 0371), and so by
Stacks 046N it remains to see that every object of `[[X/G]]` lies fppf locally in the essential
image. Over a member `f : V ⟶ U` of a covering on which the torsor `P` has a section `s`, the
trivial quadruple at the point `φ(s)` of `X` is sent to a triple with a global section mapping to
`φ(s)`, and two triples with global sections of the same image are related by a morphism over
`f` (`AlgebraicGeometry.AbstractGroupQuotientStack.exists_hom_of_sections`).

## Main results

* `AlgebraicGeometry.AbstractGroupQuotientStack.totalToTarget_totalSmul_down`: the equivariant
  map of a triple is equivariant for all sections of the constant sheaf, which are locally
  constant.
* `AlgebraicGeometry.AbstractGroupQuotientStack.exists_hom_of_sections`: a morphism out of a
  triple with a global section.
* `AlgebraicGeometry.nonempty_isEquivalenceOver_of_constantGroupData`: the comparison functor is
  an equivalence over the site, for any identification of the acting group with the constant
  sheaf compatible with `ρ`.
* `AlgebraicGeometry.nonempty_isEquivalenceOver_abstractGroupQuotientStack`: **Stacks 0371**, the
  last clause.

## References

* [Stacks Project, Tag 0371](https://stacks.math.columbia.edu/tag/0371)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
* [Stacks Project, Tag 0370](https://stacks.math.columbia.edu/tag/0370)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory MonObj

universe t v u

namespace AlgebraicGeometry

open Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {G : Type (max (u + 1) v)} [Group G] [Small.{u} G]
  [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat.{max (u + 1) v}]

variable (hG : 𝒞.Contains (constantGroupScheme G S).X.left)

/-! ### Sections of the constant sheaf of groups are locally constant -/

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- A section of the constant sheaf of groups is determined by its values at the points. -/
theorem ptFun_injective {T : BigFppfOver 𝒞 S hS}
    {a b : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op T)}
    (h : ∀ z, ptFun hG (V := T) a z = ptFun hG (V := T) b z) : a = b :=
  (constPointsEquiv hG T).injective (LocallyConstant.coe_injective (funext h))

/-- **A section of the constant sheaf of groups is, locally, a constant section.** -/
theorem exists_unit_locally {T : BigFppfOver 𝒞 S hS}
    (cγ : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj (op T)) :
    lcSieve (ptFun hG (cspFun hG T cγ)) ∈ BigFppfOver.topology 𝒞 S hS T ∧
      ∀ ⦃Z : BigFppfOver 𝒞 S hS⦄ (k : Z ⟶ T) (g : G),
        (∀ z, ptFun hG (cspFun hG T cγ) (schMap k z) = g) →
        (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.map k.op cγ =
          constantSheafOfGroupsUnit (BigFppfOver.topology 𝒞 S hS) G (op Z) g := by
  refine ⟨lcSieve_mem (isLocallyConstant_ptFun hG _), fun Z k g hg => cspFun_injective hG Z ?_⟩
  refine ptFun_injective hG (fun z => ?_)
  rw [constSheafPts_map, ptFun_map, hg]
  exact (ptFun_constSheafPts_unit hG Z g z).symm

/-! ### Equivariance of an object of `[[X/G]]` for all sections of the constant sheaf -/

variable {X₀ : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
  (hX₀ : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) X₀) (ρ₀ : G →* Aut X₀)

namespace AbstractGroupQuotientStack

universe t₁ t₂

/-- The equivariant map of an object of `[[X/G]]` is equivariant for *every* section of the
constant sheaf of groups, which acts on `X` through `G_S`; the definition asks this of the
constant sections only. -/
theorem totalToTarget_totalSmul_down
    (A : AbstractGroupQuotientStack.{t₁} 𝒞 S hS G (X₀ ⋙ uliftFunctor.{t₂})
      (uliftAction.{t₂} ρ₀))
    (V : BigFppfOver 𝒞 S hS)
    (c : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj (op V))
    (p : A.Total (op V)) :
    (A.totalToTarget (op V) (A.totalSmul c p)).down =
      actGlue hG hX₀ ρ₀ (cspFun hG V c) (A.totalToTarget (op V) p).down := by
  refine eq_of_mem_topology hX₀ (exists_unit_locally hG c).1 ?_
  rintro Z k ⟨g, hg⟩
  have hc := (exists_unit_locally hG c).2 k g hg
  rw [actGlue_spec hG hX₀ ρ₀ _ _ k g hg]
  have e1 := congrArg ULift.down (A.totalToTarget_naturality k.op (A.totalSmul c p))
  have e2 := congrArg ULift.down (A.totalToTarget_naturality k.op p)
  change _ = X₀.map k.op _ at e1
  change _ = X₀.map k.op _ at e2
  rw [← e1, ← e2]
  have e3 : A.totalMap k.op (A.totalSmul c p) = A.totalSmul
      (constantSheafOfGroupsUnit (BigFppfOver.topology 𝒞 S hS) G (op Z) g)
        (A.totalMap k.op p) := by
    rw [← hc]
    exact SheafOfGroups.Torsors.totalMap_totalSmul A.toTorsors k.op c p
  rw [e3, totalToTarget_totalSmul]
  rfl

section HomOfSections

variable {A₁ A : AbstractGroupQuotientStack.{t₁} 𝒞 S hS G (X₀ ⋙ uliftFunctor.{t₂})
  (uliftAction.{t₂} ρ₀)}

omit [Small.{u} G] in
/-- The action of the constant sheaf of groups on the total space is multiplicative. -/
theorem totalSmul_mul' (A : AbstractGroupQuotientStack.{t₁} 𝒞 S hS G (X₀ ⋙ uliftFunctor.{t₂})
      (uliftAction.{t₂} ρ₀)) {V : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    (cγ δ : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj V)
    (p : A.Total V) : A.totalSmul (cγ * δ) p = A.totalSmul cγ (A.totalSmul δ p) :=
  congrArg (fun s => (⟨p.1, s⟩ : A.Total V)) (A.torsor.mul_act (op (Over.mk p.1)) cγ δ p.2)

omit [Small.{u} G] in
/-- Simple transitivity on the total space, for a non-commutative group: two sections over
the same morphism differ by a unique section of the constant sheaf of groups. -/
theorem existsUnique_smul_total (A : AbstractGroupQuotientStack.{t₁} 𝒞 S hS G
      (X₀ ⋙ uliftFunctor.{t₂}) (uliftAction.{t₂} ρ₀)) {V : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    (p q : A.Total V) (h : q.1 = p.1) :
    ∃! cγ : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj V,
      A.totalSmul cγ p = q := by
  obtain ⟨a, x⟩ := p
  obtain ⟨b, y⟩ := q
  obtain rfl : b = a := h
  obtain ⟨cγ, hcγ, hu⟩ := A.torsor.simplyTransitive (op (Over.mk b)) ⟨x⟩ x y
  refine ⟨cγ, congrArg (Sigma.mk b) hcγ, fun δ hδ => hu δ ?_⟩
  exact eq_of_heq (Sigma.mk.inj hδ).2

/-- The restriction of a global section `σ` of `A₁` along the base component of `p`. -/
abbrev secRes (σ : A₁.Total (op A₁.base)) {W : (BigFppfOver 𝒞 S hS)ᵒᵖ} (p : A₁.Total W) :
    A₁.Total W :=
  A₁.totalMap p.1.op σ

omit [Small.{u} G] in
/-- If `σ` lies over the identity, then `secRes σ p` has the same base component as `p`. -/
theorem secRes_fst (σ : A₁.Total (op A₁.base)) (hσ : σ.1 = 𝟙 _) {W : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    (p : A₁.Total W) : (secRes ρ₀ σ p).1 = p.1 := by
  change p.1 ≫ σ.1 = p.1
  rw [hσ, Category.comp_id]

/-- The section of the constant sheaf of groups carrying `σ` to `p`. -/
def ratio (σ : A₁.Total (op A₁.base)) (hσ : σ.1 = 𝟙 _) {W : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    (p : A₁.Total W) :
    (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj W :=
  (existsUnique_smul_total ρ₀ A₁ (secRes ρ₀ σ p) p (secRes_fst ρ₀ σ hσ p).symm).choose

omit [Small.{u} G] in
/-- The section `ratio σ hσ p` carries `secRes σ p` to `p`. -/
theorem ratio_spec (σ : A₁.Total (op A₁.base)) (hσ : σ.1 = 𝟙 _) {W : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    (p : A₁.Total W) : A₁.totalSmul (ratio ρ₀ σ hσ p) (secRes ρ₀ σ p) = p :=
  (existsUnique_smul_total ρ₀ A₁ (secRes ρ₀ σ p) p (secRes_fst ρ₀ σ hσ p).symm).choose_spec.1

omit [Small.{u} G] in
/-- `ratio σ hσ p` is the unique section carrying `secRes σ p` to `p`. -/
theorem ratio_unique (σ : A₁.Total (op A₁.base)) (hσ : σ.1 = 𝟙 _) {W : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    (p : A₁.Total W) (c : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj W)
    (hc : A₁.totalSmul c (secRes ρ₀ σ p) = p) : c = ratio ρ₀ σ hσ p :=
  (existsUnique_smul_total ρ₀ A₁ (secRes ρ₀ σ p) p (secRes_fst ρ₀ σ hσ p).symm).unique hc
    (ratio_spec ρ₀ σ hσ p)

omit [Small.{u} G] in
/-- `ratio` commutes with restriction along a morphism. -/
theorem ratio_map (σ : A₁.Total (op A₁.base)) (hσ : σ.1 = 𝟙 _) {W W' : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    (h : W ⟶ W') (p : A₁.Total W) :
    ratio ρ₀ σ hσ (A₁.totalMap h p) =
      (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.map h
        (ratio ρ₀ σ hσ p) := by
  refine (ratio_unique ρ₀ σ hσ _ _ ?_).symm
  have e := SheafOfGroups.Torsors.totalMap_totalSmul A₁.toTorsors h (ratio ρ₀ σ hσ p)
    (secRes ρ₀ σ p)
  have e' := SheafOfGroups.Torsors.totalMap_comp A₁.toTorsors p.1.op h σ
  change A₁.totalMap h (A₁.totalSmul _ _) =
    A₁.totalSmul _ (A₁.totalMap h (A₁.totalMap p.1.op σ)) at e
  change A₁.totalMap h (A₁.totalMap p.1.op σ) = A₁.totalMap (p.1.op ≫ h) σ at e'
  change A₁.totalSmul _ (A₁.totalMap (p.1.op ≫ h) σ) = _
  rw [← e', ← e, ratio_spec]

omit [Small.{u} G] in
/-- The ratio of `c · p` is `c` times the ratio of `p`. -/
theorem ratio_smul (σ : A₁.Total (op A₁.base)) (hσ : σ.1 = 𝟙 _) {W : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    (c : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj W)
    (p : A₁.Total W) :
    ratio ρ₀ σ hσ (A₁.totalSmul c p) = c * ratio ρ₀ σ hσ p := by
  refine (ratio_unique ρ₀ σ hσ _ _ ?_).symm
  rw [totalSmul_mul']
  exact congrArg (A₁.totalSmul c) (ratio_spec ρ₀ σ hσ p)

/-- The morphism `A₁ ⟶ A` attached to global sections: `cγ · σ ↦ cγ · s`. -/
def secMap (σ : A₁.Total (op A₁.base)) (hσ : σ.1 = 𝟙 _) (s : A.Total (op A₁.base))
    {W : (BigFppfOver 𝒞 S hS)ᵒᵖ} (p : A₁.Total W) : A.Total W :=
  A.totalSmul (ratio ρ₀ σ hσ p) (A.totalMap p.1.op s)

omit [Small.{u} G] in
/-- Restriction on the total space is equivariant for the action of the constant sheaf of
groups. -/
theorem totalMap_totalSmul' (A : AbstractGroupQuotientStack.{t₁} 𝒞 S hS G
      (X₀ ⋙ uliftFunctor.{t₂}) (uliftAction.{t₂} ρ₀)) {V W : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    (h : V ⟶ W) (cγ : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj V)
    (p : A.Total V) :
    A.totalMap h (A.totalSmul cγ p) =
      A.totalSmul ((constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.map h cγ)
        (A.totalMap h p) :=
  SheafOfGroups.Torsors.totalMap_totalSmul A.toTorsors h cγ p

omit [Small.{u} G] in
/-- Restriction on the total space along `h` and then `k` is restriction along `h ≫ k`. -/
theorem totalMap_comp' (A : AbstractGroupQuotientStack.{t₁} 𝒞 S hS G
      (X₀ ⋙ uliftFunctor.{t₂}) (uliftAction.{t₂} ρ₀)) {W W' W'' : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    (h : W ⟶ W') (k : W' ⟶ W'') (r : A.Total W) :
    A.totalMap k (A.totalMap h r) = A.totalMap (h ≫ k) r :=
  SheafOfGroups.Torsors.totalMap_comp A.toTorsors h k r

include hX₀ hG in
/-- **A morphism out of an object of `[[X/G]]` with a global section.** If `A₁` has a section
`σ` over its base and `A` has a section `s` over `f : A₁.base ⟶ A.base` with the same image in
`X`, there is a morphism `A₁ ⟶ A` lying over `f`. -/
theorem exists_hom_of_sections (f : A₁.base ⟶ A.base) (σ : A₁.Total (op A₁.base))
    (hσ : σ.1 = 𝟙 _) (s : A.Total (op A₁.base)) (hs : s.1 = f)
    (h : A₁.totalToTarget _ σ = A.totalToTarget _ s) :
    ∃ m : A₁ ⟶ A, Hom.base m = f := by
  have hsec : ∀ (a : A₁.base ⟶ A₁.base) {W : BigFppfOver 𝒞 S hS} (b : W ⟶ A₁.base),
      (A.totalToTarget (op W) (A.totalMap b.op s)).down =
        (A₁.totalToTarget (op W) (A₁.totalMap b.op σ)).down := by
    intro _ W b
    rw [A.totalToTarget_naturality, A₁.totalToTarget_naturality, h]
  refine ⟨{ base := f
            map := fun W p => secMap ρ₀ σ hσ s p
            map_naturality := ?_
            map_equivariant := ?_
            bijOn_map := ?_
            totalToTarget_comp := ?_ }, rfl⟩
  · intro W W' k p
    change A.totalSmul _ (A.totalMap (k.unop ≫ p.1).op s) =
      A.totalMap k (A.totalSmul _ (A.totalMap p.1.op s))
    rw [totalMap_totalSmul', ratio_map, totalMap_comp']
    rfl
  · intro W c p
    change A.totalSmul _ (A.totalMap p.1.op s) = A.totalSmul c (A.totalSmul _ _)
    rw [ratio_smul, totalSmul_mul']
  · intro W a
    refine ⟨fun p hp => ?_, fun p hp p' hp' hpp => ?_, fun q hq => ?_⟩
    · change p.1 ≫ s.1 = a ≫ f
      rw [hs, show p.1 = a from hp]
    · rw [← ratio_spec ρ₀ σ hσ p, ← ratio_spec ρ₀ σ hσ p']
      obtain ⟨b, x⟩ := p
      obtain ⟨b', x'⟩ := p'
      have e1 : b = a := hp
      have e2 : b' = a := hp'
      subst e1 e2
      have hu := existsUnique_smul_total ρ₀ A (A.totalMap _ s)
        (secMap ρ₀ σ hσ s (⟨_, x⟩ : A₁.Total W)) rfl
      rw [hu.unique rfl hpp.symm]
    · obtain ⟨c, hc, -⟩ := existsUnique_smul_total ρ₀ A (A.totalMap a.op s) q (by
        rw [show q.1 = a ≫ f from hq]
        change a ≫ f = a ≫ s.1
        rw [hs])
      refine ⟨A₁.totalSmul c (A₁.totalMap a.op σ), ?_, ?_⟩
      · change a ≫ σ.1 = a
        rw [hσ]
        exact Category.comp_id a
      · have hr := (ratio_unique ρ₀ σ hσ (A₁.totalSmul c (A₁.totalMap a.op σ)) c (by
          change A₁.totalSmul c (A₁.totalMap (a ≫ σ.1).op σ) = _
          rw [hσ]
          simp only [Category.comp_id])).symm
        change A.totalSmul _ (A.totalMap (a ≫ σ.1).op s) = q
        rw [hr, hσ]
        simp only [Category.comp_id]
        exact hc
  · intro W p
    apply ULift.ext
    change (A.totalToTarget (op W.unop) (A.totalSmul _ _)).down = _
    rw [totalToTarget_totalSmul_down hG hX₀ ρ₀ A W.unop, hsec (𝟙 _) p.1]
    conv_rhs => rw [← ratio_spec ρ₀ σ hσ p]
    rw [totalToTarget_totalSmul_down hG hX₀ ρ₀ A₁ W.unop]

end HomOfSections

end AbstractGroupQuotientStack

/-! ### The trivial quadruple at a point -/

section Trivial

variable {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
  (Gr : GroupAlgebraicSpace 𝒞 S hS B hB)

/-- The unit section of `G_V` over `V`, as a section of the total space of the trivial
torsor. -/
abbrev unitSec (V : BigFppfOver 𝒞 S hS) (b : yoneda.obj V ⟶ B) :
    (pullbackGroup hB Gr V b).obj.X.left.obj (op V) :=
  yonedaEquiv (1 : sliceOver (Over.mk (𝟙 V)) ⟶ (pullbackGroup hB Gr V b).obj.X).left

omit [Small.{u} G] in
omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- The unit section `unitSec V b` lies over the identity of `V`. -/
theorem unitSec_over (V : BigFppfOver 𝒞 S hS) (b : yoneda.obj V ⟶ B) :
    (pullback.snd Gr.obj.X.hom b).app (op V) (unitSec Gr V b) = 𝟙 V := by
  refine (yonedaEquiv_comp _ _).symm.trans ?_
  refine (congrArg yonedaEquiv (pbLeft_snd Gr _)).trans ?_
  exact yonedaEquiv_yoneda_map _

omit [Small.{u} G] in
omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- **The map of the trivial quadruple at a point `x` sends the unit section to `x`.** -/
theorem trivialTorsorMap_unitSec (Xo : Over B) [ModObj Gr.obj.X Xo] (V : BigFppfOver 𝒞 S hS)
    (ξ : yoneda.obj V ⟶ Xo.left) :
    (trivialTorsorMap hB Gr Xo V ξ).app (op V) (unitSec Gr V (ξ ≫ Xo.hom)) = yonedaEquiv ξ := by
  set b := ξ ≫ Xo.hom with hb
  set k := (1 : sliceOver (Over.mk (𝟙 V)) ⟶ (pullbackGroup hB Gr V b).obj.X) with hk
  have hm : baseChangePts Gr V b (Over.mk (𝟙 V)) k = 1 := map_one _
  let ξ' : (Over.mk (yoneda.map (Over.mk (𝟙 V)).hom ≫ b) : Over B) ⟶ Xo :=
    Over.homMk (yoneda.map (𝟙 V) ≫ ξ) (by
      change yoneda.map (𝟙 V) ≫ ξ ≫ Xo.hom = yoneda.map (𝟙 V) ≫ b
      rw [hb])
  have key : pbLeft Gr k ≫ trivialTorsorMap hB Gr Xo V ξ =
      (CartesianMonoidalCategory.lift (baseChangePts Gr V b (Over.mk (𝟙 V)) k)
        ξ' ≫ γ[Gr.obj.X, Xo]).left := by
    rw [Over.comp_left, Over.lift_left]
    refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ?_)
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      rfl
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
        pbLeft_snd]
      rfl
  have h1 : (CartesianMonoidalCategory.lift (baseChangePts Gr V b (Over.mk (𝟙 V)) k) ξ' ≫
      γ[Gr.obj.X, Xo]) = ξ' := by
    rw [hm, ← Hom.smul_def, one_smul]
  refine (yonedaEquiv_comp _ _).symm.trans ?_
  change yonedaEquiv (pbLeft Gr k ≫ _) = _
  rw [key, h1]
  change yonedaEquiv (yoneda.map (𝟙 V) ≫ ξ) = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

end Trivial

/-! ### The equivalence -/

section Equivalence

variable (hX : IsAlgebraicSpace 𝒞 S hS X₀)
  {Gr : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS)}
  [ModObj Gr.obj.X (overBaseS X₀)] (D : ConstantGroupData (isAlgebraicSpace_baseS 𝒞 S hS) Gr G)
  (hρ : IsCompatibleAction (X := overBaseS X₀) D (uliftAction.{max t (u + 1)} ρ₀))

include hX hG in
/-- **An identification of `G_U` with the constant sheaf, compatible with `ρ`, makes the
comparison `[[X/𝒢]] ⥤ [[X/G]]` an equivalence over `(Sch/S)_fppf`.** -/
theorem nonempty_isEquivalenceOver_of_constantGroupData :
    Nonempty (Functor.IsEquivalenceOver
      (TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS) Gr (overBaseS X₀))
      (AbstractGroupQuotientStack.projection :
        AbstractGroupQuotientStack.{max t (u + 1)} 𝒞 S hS G (X₀ ⋙ uliftFunctor.{max t (u + 1)})
          (uliftAction.{max t (u + 1)} ρ₀) ⥤ _)
      (torsorWithMapToAbstractQuotient.{max t (u + 1)} D hρ)) := by
  let q : AbstractGroupQuotientStack.{max t (u + 1)} 𝒞 S hS G (X₀ ⋙ uliftFunctor.{max t (u + 1)})
      (uliftAction.{max t (u + 1)} ρ₀) ⥤ _ := AbstractGroupQuotientStack.projection
  have hX' : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) (X₀ ⋙ uliftFunctor.{max t (u + 1)}) :=
    (isSheaf_iff_isSheaf_of_type _ _).2
      (Presieve.isSheaf_comp_uliftFunctor _ ((isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf))
  have hq : q.IsFiberedInGroupoids :=
    AbstractGroupQuotientStack.projection_isFiberedInGroupoids
  have hp : (TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS) Gr
      (overBaseS X₀)).IsFiberedInGroupoids :=
    TorsorWithMap.projection_isFiberedInGroupoids _ (torsorProjection_isFiberedInGroupoids _ _)
  have := hp.isFibered
  have hp' : Functor.IsStackInGroupoids.{u + 1}
      (TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS) Gr (overBaseS X₀))
      (BigFppfOver.topology 𝒞 S hS) :=
    TorsorWithMap.projection_isStackInGroupoids_of_isAlgebraicSpace
      (isAlgebraicSpace_baseS 𝒞 S hS) Gr (overBaseS X₀) hX
  have h₁ := Functor.isStack_of_isStackInGroupoids hp'
  have h₂ : q.IsStack (BigFppfOver.topology 𝒞 S hS) :=
    AbstractGroupQuotientStack.projection_isStack_of_isSheaf hX'
  have hF : Functor.IsFibredOneMorphism _ _
      (torsorWithMapToAbstractQuotient.{max t (u + 1)} D hρ) :=
    { comp_eq := torsorWithMapToAbstractQuotient_comp_projection _ _
      map_isStronglyCartesian := by
        intro R T f a b φ hφ
        have := hφ.toIsHomLift
        exact Functor.isStronglyCartesian_of_isFiberedInGroupoids hq f _
          (Functor.isHomLift_map_of_comp_eq
            (torsorWithMapToAbstractQuotient_comp_projection D hρ) f φ) }
  have := torsorWithMapToAbstractQuotient_full D hρ (fun U b b' => baseS_ext b b')
  have := torsorWithMapToAbstractQuotient_faithful D hρ
  rw [Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers h₁ h₂ hF]
  rintro U ⟨A, rfl⟩
  obtain ⟨R, hR, hne⟩ := A.isTorsor (Over.mk (𝟙 A.base))
  refine ⟨Sieve.overEquiv _ R, hR, ?_⟩
  intro V f hf
  have hf' := (Sieve.overEquiv_iff R (f : V ⟶ A.base)).1 hf
  obtain ⟨s₀⟩ := hne hf'
  let sT : A.Total (op V) := ⟨f ≫ 𝟙 A.base, s₀⟩
  set x₀ : X₀.obj (op V) := (A.totalToTarget (op V) sT).down with hx₀
  set ξ : yoneda.obj V ⟶ (overBaseS X₀).left := yonedaEquiv.symm x₀ with hξ
  let z := trivialTorsorWithMap (isAlgebraicSpace_baseS 𝒞 S hS) Gr (overBaseS X₀) V ξ
  let Fz := (torsorWithMapToAbstractQuotient.{max t (u + 1)} D hρ).obj z
  let σ : Fz.Total (op V) := TorsorObj.totalSectionOf.{max t (u + 1)} D z.toTorsorObj
    (unitSec Gr V (ξ ≫ (overBaseS X₀).hom))
  have hσ : σ.1 = 𝟙 V := unitSec_over Gr V _
  have htgt : Fz.totalToTarget (op V) σ = A.totalToTarget (op V) sT := by
    apply ULift.ext
    change (trivialTorsorMap (isAlgebraicSpace_baseS 𝒞 S hS) Gr (overBaseS X₀) V ξ).app (op V)
      (unitSec Gr V (ξ ≫ (overBaseS X₀).hom)) = x₀
    rw [trivialTorsorMap_unitSec, hξ, Equiv.apply_symm_apply]
  obtain ⟨m, hm⟩ := AbstractGroupQuotientStack.exists_hom_of_sections hG hX.isSheaf ρ₀
    (A₁ := Fz) (A := A) f σ hσ sT (Category.comp_id f) htgt
  have := h₂.isFibered
  have hlift : q.IsHomLift f m :=
    IsHomLift.of_fac' _ f m rfl rfl (by
      change AbstractGroupQuotientStack.Hom.base m = 𝟙 V ≫ f ≫ 𝟙 A.base
      exact hm.trans ((Category.comp_id f).symm.trans (Category.id_comp _).symm))
  have hpc := Functor.IsPreFibered.pullbackMap.IsCartesian (p := q) (rfl : q.obj A = A.base) f
  have hmc : q.IsCartesian f m := by
    have := Functor.isStronglyCartesian_of_isFiberedInGroupoids hq f m hlift
    infer_instance
  let e := @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _ q _ _ _ _ f
    (Functor.IsPreFibered.pullbackMap (p := q) (rfl : q.obj A = A.base) f) hpc _ m hmc
  exact ⟨⟨z, rfl⟩, ⟨Functor.Fiber.isoMk e
    (@Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ q _ _ _ _ f
      (Functor.IsPreFibered.pullbackMap (p := q) (rfl : q.obj A = A.base) f) hpc _ m hmc)⟩⟩

/-- **The comparison functor `[[X/G_S]] ⥤ [[X/G]]` of Stacks 0371.** -/
abbrev constComparison :
    letI := constGSModObj hG hX.isSheaf ρ₀
    TorsorWithMap (isAlgebraicSpace_baseS 𝒞 S hS) (constGS (hS := hS) hG) (overBaseS X₀) ⥤
      AbstractGroupQuotientStack.{max t (u + 1)} 𝒞 S hS G (X₀ ⋙ uliftFunctor.{max t (u + 1)})
        (uliftAction.{max t (u + 1)} ρ₀) :=
  let := constGSModObj hG hX.isSheaf ρ₀
  torsorWithMapToAbstractQuotient.{max t (u + 1)} (constGSData hG)
    (constGS_isCompatibleAction.{max t (u + 1)} hG hX.isSheaf ρ₀)

/-- The comparison functor `constComparison` is an equivalence over `(Sch/S)_fppf`. -/
theorem nonempty_isEquivalenceOver_constComparison :
    letI := constGSModObj hG hX.isSheaf ρ₀
    Nonempty (Functor.IsEquivalenceOver
      (TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS) (constGS (hS := hS) hG)
        (overBaseS X₀))
      (AbstractGroupQuotientStack.projection :
        AbstractGroupQuotientStack.{max t (u + 1)} 𝒞 S hS G (X₀ ⋙ uliftFunctor.{max t (u + 1)})
          (uliftAction.{max t (u + 1)} ρ₀) ⥤ _)
      (constComparison.{t} hG ρ₀ hX)) :=
  let := constGSModObj hG hX.isSheaf ρ₀
  nonempty_isEquivalenceOver_of_constantGroupData.{t} hG ρ₀ hX (constGSData hG)
    (constGS_isCompatibleAction.{max t (u + 1)} hG hX.isSheaf ρ₀)

/-- Let `G` be an abstract group whose constant group scheme `G_S` lies in the big fppf site,
`X` an algebraic space over `S` and `ρ : G →* Aut X` an action. Then the stack `[[X/G]]` of
triples `(U, P, φ)`, `P` a torsor under the constant sheaf `G` on `(Sch/U)_fppf` and
`φ : P → X` equivariant, is equivalent over `(Sch/S)_fppf` to the stack `[[X/G_S]]`, for `G_S`
the constant group algebraic space `AlgebraicGeometry.Space.constantGroupSpace` acting on `X`
through `ρ` (`AlgebraicGeometry.Space.constGSModObj`, whose constant sections act as `ρ` does by
`AlgebraicGeometry.Space.constGS_isCompatibleAction`). -/
@[stacks 0371 "the equivalence of [[X/G]] with [[X/G_S]]"]
theorem nonempty_isEquivalenceOver_abstractGroupQuotientStack :
    letI : ModObj (constantGroupSpace 𝒞 S hS G (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS)
        hG).obj.X (overBaseS X₀) := constGSModObj hG hX.isSheaf ρ₀
    ∃ F : TorsorWithMap (isAlgebraicSpace_baseS 𝒞 S hS)
        (constantGroupSpace 𝒞 S hS G (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS) hG)
        (overBaseS X₀) ⥤
      AbstractGroupQuotientStack.{max t (u + 1)} 𝒞 S hS G (X₀ ⋙ uliftFunctor.{max t (u + 1)})
        (uliftAction.{max t (u + 1)} ρ₀),
      Nonempty (Functor.IsEquivalenceOver
        (TorsorWithMap.projection (isAlgebraicSpace_baseS 𝒞 S hS)
          (constantGroupSpace 𝒞 S hS G (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS) hG)
          (overBaseS X₀))
        AbstractGroupQuotientStack.projection F) :=
  ⟨constComparison.{t} hG ρ₀ hX, nonempty_isEquivalenceOver_constComparison.{t} hG ρ₀ hX⟩

end Equivalence

end AlgebraicGeometry
