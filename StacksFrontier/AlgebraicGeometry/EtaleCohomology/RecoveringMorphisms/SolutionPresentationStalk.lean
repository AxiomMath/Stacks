module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.SolutionPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.TargetSitePoint
public import StacksFrontier.CategoryTheory.Sites.Point.FlatModuleStalk

/-!
# The stalk of a solution sheaf is the solution set of the stalk

Step (4) of the proof of [Stacks Project, Tag 04I6] checks that the comparison
`g⁻¹h_V ⟶ h_{X ×_Y V}` of step (3) is an isomorphism by computing both sides at a point of
`X_étale`, where the answer is the set of solutions of the presented system in a strictly
henselian local ring and the comparison is pushforward of solutions along a local homomorphism.
This file computes one of those two stalks, in the form which
`AlgebraicGeometry.SolutionPresentation` makes common to the source and the target: for a sheaf
on the small étale site of `S` presented as the solutions of a system `P` over `R` relative to
`ψ : R ⟶ Γ(S, ⊤)`, the stalk at a point `p` of the site is the set of solutions of `P` in the
stalk ring `𝒪_{S,p}`, with coefficients pushed along `ψ` and the germ map.

Filtered colimits of sets commute with the finitary condition of being a solution, which is what
the two halves of the bijectivity statement verify by hand: finitely many germs are germs of
sections over one neighbourhood (`Stacks.exists_toPresheafFiber_fin`), and finitely many
equalities of germs are realized by restriction to one neighbourhood
(`AlgebraicGeometry.exists_restrict_eq_of_forall_germ_eq`).

## Main definitions

* `AlgebraicGeometry.smallEtaleGermHom` — the germ map `Γ(U, ⊤) ⟶ 𝒪_{S,p}` at a point of the
  site, as a ring homomorphism.
* `AlgebraicGeometry.smallEtaleStalkCoeff` — the coefficient map `R ⟶ 𝒪_{S,p}` of the system at a
  point of the site, namely `ψ` followed by a germ map.
* `AlgebraicGeometry.stalkSolutionSet` — the solutions of the system in the stalk ring.
* `AlgebraicGeometry.SolutionPresentation.stalkSolution` — the map from the stalk of `h_W` to the
  solutions of the system in the stalk ring, sending the germ of a chart-valued point of `W` to
  the germs of its coordinates.

## Main results

* `AlgebraicGeometry.smallEtaleGermHom_comp_smallEtaleCoeff` — the coefficient map of a chart,
  followed by the germ map at a point of the site lying over that chart, does not depend on the
  chart: it is `AlgebraicGeometry.smallEtaleStalkCoeff`.
* `AlgebraicGeometry.SolutionPresentation.bijective_stalkSolution` — **the stalk of a solution
  sheaf is the solution set of the stalk.**

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Evaluation of a transported system -/

namespace MvPolynomial

/-- Pushing a polynomial system and a point along a ring map commutes with evaluation.  This is
the computation behind `MvPolynomial.isSolution_comp`, isolated so that it can also be used in
the converse direction. -/
theorem eval_map_ringHom_comp {R A A' : Type*} [CommRing R] [CommRing A] [CommRing A']
    {σ : Type*} (g : R →+* A) (ρ : A →+* A') (a : σ → A) (q : MvPolynomial σ R) :
    MvPolynomial.eval (fun i => ρ (a i)) (MvPolynomial.map (ρ.comp g) q) =
      ρ (MvPolynomial.eval a (MvPolynomial.map g q)) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_comp_left ρ g a q]
  rfl

end MvPolynomial

namespace AlgebraicGeometry

/-! ### Finitely many equalities of germs are realized on one neighbourhood -/

section Refinement

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C} [LocallySmall.{u} C]
  (Φ : J.Point.{u}) {A : Type (u + 1)} [Category.{u} A] [HasColimitsOfSize.{u, u} A]
  {FC : A → A → Type*} {CC : A → Type u} [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{u} A FC] [PreservesFilteredColimitsOfSize.{u, u} (forget A)]

/-- **Finitely many equalities of germs are realized by restriction to one neighbourhood.**  If
`l` pairs of sections of a presheaf over a chart `X` have equal germs at a point of the site
lying over `X`, then there is a single refinement of `X` through that point on which all `l`
pairs agree.

The induction refines for one index at a time and restricts the remaining sections before
appealing to the inductive hypothesis, so that the refinements compose rather than having to be
merged. -/
theorem exists_restrict_eq_of_forall_germ_eq (P : Cᵒᵖ ⥤ A) :
    ∀ (l : ℕ) (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : Fin l → ToType (P.obj (op X))),
      (∀ i, Φ.toPresheafFiber X x P (z₁ i) = Φ.toPresheafFiber X x P (z₂ i)) →
      ∃ (Y : C) (f : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map f y = x ∧
        ∀ i, P.map f.op (z₁ i) = P.map f.op (z₂ i) := by
  intro l
  induction l with
  | zero =>
      intro X x _ _ _
      exact ⟨X, CategoryStruct.id X, x, by simp, fun i => i.elim0⟩
  | succ l ih =>
      intro X x z₁ z₂ h
      obtain ⟨Y₀, f₀, y₀, hy₀, h₀⟩ := (Φ.toPresheafFiber_eq_iff' X x (z₁ 0) (z₂ 0)).1 (h 0)
      have hgerm : ∀ i : Fin l,
          Φ.toPresheafFiber Y₀ y₀ P (P.map f₀.op (z₁ i.succ)) =
            Φ.toPresheafFiber Y₀ y₀ P (P.map f₀.op (z₂ i.succ)) := by
        intro i
        simp only [Φ.toPresheafFiber_w_apply, hy₀]
        exact h i.succ
      obtain ⟨Y₁, f₁, y₁, hy₁, h₁⟩ := ih Y₀ y₀ (fun i => P.map f₀.op (z₁ i.succ))
        (fun i => P.map f₀.op (z₂ i.succ)) hgerm
      refine ⟨Y₁, f₁ ≫ f₀, y₁, ?_, ?_⟩
      · rw [Φ.fiber.map_comp, ConcreteCategory.comp_apply, hy₁, hy₀]
      · intro i
        simp only [op_comp, P.map_comp, ConcreteCategory.comp_apply]
        induction i using Fin.cases with
        | zero => exact congrArg _ h₀
        | succ j => exact h₁ j

end Refinement

section RefinementRing

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C} [LocallySmall.{u} C]
  (Φ : J.Point.{u})

/-- **A germ vanishes only if the section vanishes on a neighbourhood**, for finitely many
sections at once.  This is `AlgebraicGeometry.exists_restrict_eq_of_forall_germ_eq` against the
zero section, in the form the solution condition needs. -/
theorem exists_restrict_eq_zero_of_forall_germ_eq_zero (O : Cᵒᵖ ⥤ CommRingCat.{u}) (X : C)
    (x : Φ.fiber.obj X) {l : ℕ} (z : Fin l → ↥(O.obj (op X)))
    (h : ∀ i, (Φ.toPresheafFiber X x O).hom (z i) = 0) :
    ∃ (Y : C) (f : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map f y = x ∧
      ∀ i, (O.map f.op).hom (z i) = 0 := by
  obtain ⟨Y, f, y, hy, hz⟩ :=
    exists_restrict_eq_of_forall_germ_eq Φ O l X x z (fun _ => (0 : ↥(O.obj (op X))))
      (fun i => by
        change (Φ.toPresheafFiber X x O).hom (z i) = (Φ.toPresheafFiber X x O).hom 0
        rw [h i, map_zero])
  refine ⟨Y, f, y, hy, fun i => ?_⟩
  have hi : (O.map f.op).hom (z i) = (O.map f.op).hom 0 := hz i
  rw [hi, map_zero]

end RefinementRing

/-! ### Germs on the small étale site -/

section Germ

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (p : (SmallEtale.topology B S hS).Point.{u})

/-- The germ map `Γ(U, ⊤) ⟶ 𝒪_{S,p}` of the structure sheaf at a point of the small étale site
lying over the chart `U`. -/
abbrev smallEtaleGerm (U : SmallEtale B S hS) (x : p.fiber.obj U) :
    Γ((SmallEtale.toScheme B S hS).obj U, ⊤) ⟶ smallEtaleStalkRing B S hS p :=
  p.toPresheafFiber U x (SmallEtale.commRingStructureSheaf B S hS).obj

/-- The germ map of `AlgebraicGeometry.smallEtaleGerm` as a ring homomorphism. -/
abbrev smallEtaleGermHom (U : SmallEtale B S hS) (x : p.fiber.obj U) :
    ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤) →+* ↥(smallEtaleStalkRing B S hS p) :=
  (smallEtaleGerm B S hS p U x).hom

/-- The restriction map of the structure sheaf of the small étale site is restriction of global
functions along the morphism of schemes. -/
theorem commRingStructureSheaf_map_hom {U U' : SmallEtale B S hS} (k : U' ⟶ U) :
    ((SmallEtale.commRingStructureSheaf B S hS).obj.map k.op).hom =
      smallEtaleRestrict B S hS k :=
  rfl

/-- The germ maps of the structure sheaf are compatible with restriction. -/
theorem smallEtaleGerm_restrict {U U' : SmallEtale B S hS} (k : U' ⟶ U) (x : p.fiber.obj U') :
    (SmallEtale.commRingStructureSheaf B S hS).obj.map k.op ≫ smallEtaleGerm B S hS p U' x =
      smallEtaleGerm B S hS p U (p.fiber.map k x) :=
  p.toPresheafFiber_w (P := (SmallEtale.commRingStructureSheaf B S hS).obj) k x

/-- The germ maps of the structure sheaf are compatible with restriction, as ring
homomorphisms. -/
theorem smallEtaleGermHom_comp_restrict {U U' : SmallEtale B S hS} (k : U' ⟶ U)
    (x : p.fiber.obj U') :
    (smallEtaleGermHom B S hS p U' x).comp (smallEtaleRestrict B S hS k) =
      smallEtaleGermHom B S hS p U (p.fiber.map k x) :=
  congrArg CommRingCat.Hom.hom (smallEtaleGerm_restrict B S hS p k x)

/-- Evaluated on an element, the germ maps are compatible with restriction. -/
private theorem smallEtaleGermHom_restrict_apply {U U' : SmallEtale B S hS} (k : U' ⟶ U)
    (x : p.fiber.obj U') (a : ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤)) :
    smallEtaleGermHom B S hS p U' x (smallEtaleRestrict B S hS k a) =
      smallEtaleGermHom B S hS p U (p.fiber.map k x) a :=
  RingHom.congr_fun (smallEtaleGermHom_comp_restrict B S hS p k x) a

variable {R : Type u} [CommRing R] (ψ : R →+* ↥Γ(S, ⊤))

/-- **The coefficients of the system at a point do not depend on the chart they are read on.**
The germ map at a point of the site lying over a chart, precomposed with that chart's
coefficient map, is the same for all charts: two of them are refined by a third, over which
both compute to the same ring map. -/
theorem smallEtaleGermHom_comp_smallEtaleCoeff_eq (U U' : SmallEtale B S hS)
    (x : p.fiber.obj U) (x' : p.fiber.obj U') :
    (smallEtaleGermHom B S hS p U x).comp (smallEtaleCoeff B S hS ψ U) =
      (smallEtaleGermHom B S hS p U' x').comp (smallEtaleCoeff B S hS ψ U') := by
  obtain ⟨W, z, g, g', hg, hg'⟩ := Stacks.exists_common_neighbourhood p x x'
  have main : ∀ (V : SmallEtale B S hS) (y : p.fiber.obj V) (k : W ⟶ V),
      p.fiber.map k z = y →
      (smallEtaleGermHom B S hS p V y).comp (smallEtaleCoeff B S hS ψ V) =
        (smallEtaleGermHom B S hS p W z).comp (smallEtaleCoeff B S hS ψ W) := by
    intro V y k hk
    rw [← smallEtaleCoeff_comp B S hS ψ k, ← RingHom.comp_assoc, ← hk,
      smallEtaleGermHom_comp_restrict B S hS p k z]
  rw [main U x g hg, main U' x' g' hg']

/-- **The coefficients of the system at a point of the small étale site.**  The ring map
`ψ : R ⟶ Γ(S, ⊤)` followed by the germ map of the structure sheaf at `p`, read over any chart of
which `p` is a point; `AlgebraicGeometry.smallEtaleGermHom_comp_smallEtaleCoeff_eq` says the
answer does not depend on the chart. -/
def smallEtaleStalkCoeff : R →+* ↥(smallEtaleStalkRing B S hS p) :=
  (smallEtaleGermHom B S hS p
      (Classical.choice (IsCofiltered.nonempty (C := p.fiber.Elements))).1
      (Classical.choice (IsCofiltered.nonempty (C := p.fiber.Elements))).2).comp
    (smallEtaleCoeff B S hS ψ
      (Classical.choice (IsCofiltered.nonempty (C := p.fiber.Elements))).1)

/-- The coefficient map of any chart, followed by the germ map at a point of the site lying over
that chart, is `AlgebraicGeometry.smallEtaleStalkCoeff`. -/
theorem smallEtaleGermHom_comp_smallEtaleCoeff (U : SmallEtale B S hS) (x : p.fiber.obj U) :
    (smallEtaleGermHom B S hS p U x).comp (smallEtaleCoeff B S hS ψ U) =
      smallEtaleStalkCoeff B S hS p ψ :=
  smallEtaleGermHom_comp_smallEtaleCoeff_eq B S hS p ψ U _ x _

/-- The solutions of a polynomial system in the stalk ring of the small étale site at a point,
the coefficients being pushed along `AlgebraicGeometry.smallEtaleStalkCoeff`. -/
abbrev stalkSolutionSet {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R) : Type u :=
  {α : Fin n → ↥(smallEtaleStalkRing B S hS p) //
    MvPolynomial.IsSolution P (smallEtaleStalkCoeff B S hS p ψ) α}

end Germ

/-! ### The stalk of a solution sheaf -/

namespace SolutionPresentation

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R : Type u} [CommRing R] {ψ : R →+* ↥Γ(S, ⊤)} {n : ℕ}
  {P : Fin n → MvPolynomial (Fin n) R} (pres : SolutionPresentation B S hS ψ P)
  (p : (SmallEtale.topology B S hS).Point.{u})

/-- The coordinates of a chart-valued point of `W`, read as germs at a point of the site, are a
solution of the presented system in the stalk ring. -/
theorem isSolution_germ_equiv (U : SmallEtale B S hS) (x : p.fiber.obj U) (f : U ⟶ pres.obj) :
    MvPolynomial.IsSolution P (smallEtaleStalkCoeff B S hS p ψ)
      (fun i => smallEtaleGermHom B S hS p U x ((pres.equiv U f).1 i)) :=
  (smallEtaleGermHom_comp_smallEtaleCoeff B S hS p ψ U x) ▸
    MvPolynomial.isSolution_comp _ (smallEtaleGermHom B S hS p U x) (pres.equiv U f).2

/-- The germs of the coordinates of a chart-valued point of `W`, as a solution in the stalk
ring. -/
def stalkSolutionFamily (U : SmallEtale B S hS) (x : p.fiber.obj U) :
    pres.sheaf.obj.obj (op U) ⟶ stalkSolutionSet B S hS p ψ P :=
  TypeCat.ofHom fun f => ⟨fun i => smallEtaleGermHom B S hS p U x ((pres.equiv U f).1 i),
    pres.isSolution_germ_equiv p U x f⟩

/-- The `i`-th coordinate of `stalkSolutionFamily` at `f` is the germ of the `i`-th coordinate of
`f`. -/
@[simp]
theorem stalkSolutionFamily_apply (U : SmallEtale B S hS) (x : p.fiber.obj U)
    (f : U ⟶ pres.obj) (i : Fin n) :
    (pres.stalkSolutionFamily p U x f).1 i =
      smallEtaleGermHom B S hS p U x ((pres.equiv U f).1 i) :=
  rfl

/-- The germs of the coordinates are compatible with restriction of the chart. -/
theorem stalkSolutionFamily_compat ⦃U U' : SmallEtale B S hS⦄ (k : U ⟶ U')
    (x : p.fiber.obj U) :
    pres.sheaf.obj.map k.op ≫ pres.stalkSolutionFamily p U x =
      pres.stalkSolutionFamily p U' (p.fiber.map k x) := by
  refine TypeCat.homEquiv.injective (funext fun f => Subtype.ext (funext fun i => ?_))
  change smallEtaleGermHom B S hS p U x ((pres.equiv U (k ≫ f)).1 i) =
    smallEtaleGermHom B S hS p U' (p.fiber.map k x) ((pres.equiv U' f).1 i)
  rw [pres.equiv_naturality k f i]
  exact smallEtaleGermHom_restrict_apply B S hS p k x _

/-- **The stalk of `h_W` at a point of the small étale site maps to the solutions of the
presented system in the stalk ring**, by taking the germs of the coordinates. -/
def stalkSolutionHom :
    (p.presheafFiber (A := Type u)).obj pres.sheaf.obj ⟶ stalkSolutionSet B S hS p ψ P :=
  p.presheafFiberDesc (pres.stalkSolutionFamily p) (pres.stalkSolutionFamily_compat p)

/-- The underlying map of `AlgebraicGeometry.SolutionPresentation.stalkSolutionHom`. -/
abbrev stalkSolution :
    ToType ((p.presheafFiber (A := Type u)).obj pres.sheaf.obj) →
      stalkSolutionSet B S hS p ψ P :=
  ConcreteCategory.hom (pres.stalkSolutionHom p)

/-- On the image of a chart-valued point `f` in the stalk, `stalkSolution` is `stalkSolutionFamily`
at `f`. -/
theorem stalkSolution_toPresheafFiber (U : SmallEtale B S hS) (x : p.fiber.obj U)
    (f : U ⟶ pres.obj) :
    pres.stalkSolution p (p.toPresheafFiber U x pres.sheaf.obj f) =
      pres.stalkSolutionFamily p U x f :=
  ConcreteCategory.congr_hom (p.toPresheafFiber_presheafFiberDesc
    (pres.stalkSolutionFamily p) (pres.stalkSolutionFamily_compat p) U x) f

/-- The `i`-th coordinate of `stalkSolution` on the image of a chart-valued point `f` in the stalk
is the germ of the `i`-th coordinate of `f`. -/
theorem stalkSolution_toPresheafFiber_coe (U : SmallEtale B S hS) (x : p.fiber.obj U)
    (f : U ⟶ pres.obj) (i : Fin n) :
    (pres.stalkSolution p (p.toPresheafFiber U x pres.sheaf.obj f)).1 i =
      smallEtaleGermHom B S hS p U x ((pres.equiv U f).1 i) := by
  rw [pres.stalkSolution_toPresheafFiber p U x f, pres.stalkSolutionFamily_apply p U x f i]

/-- The map of `AlgebraicGeometry.SolutionPresentation.stalkSolution` is injective: two germs of
chart-valued points of `W` with the same coordinate germs agree after restriction to a smaller
chart, by `AlgebraicGeometry.exists_restrict_eq_of_forall_germ_eq`, and the presentation is a
bijection on each chart. -/
theorem injective_stalkSolution : Function.Injective (pres.stalkSolution p) := by
  intro t₁ t₂ h
  obtain ⟨U, x, e₁, e₂, rfl, rfl⟩ :=
    p.toPresheafFiber_jointly_surjective₂ (P := pres.sheaf.obj) t₁ t₂
  let f₁ : U ⟶ pres.obj := e₁
  let f₂ : U ⟶ pres.obj := e₂
  have hco : ∀ i, smallEtaleGermHom B S hS p U x ((pres.equiv U f₁).1 i) =
      smallEtaleGermHom B S hS p U x ((pres.equiv U f₂).1 i) := by
    intro i
    rw [← pres.stalkSolution_toPresheafFiber_coe p U x f₁ i,
      ← pres.stalkSolution_toPresheafFiber_coe p U x f₂ i]
    exact congrFun (congrArg Subtype.val h) i
  obtain ⟨W, k, z, hz, hk⟩ :=
    exists_restrict_eq_of_forall_germ_eq p (SmallEtale.commRingStructureSheaf B S hS).obj n U x
      (fun i => (pres.equiv U f₁).1 i) (fun i => (pres.equiv U f₂).1 i) hco
  have hcomp : k ≫ f₁ = k ≫ f₂ :=
    (pres.equiv W).injective (Subtype.ext (funext fun i => by
      rw [pres.equiv_naturality k f₁ i, pres.equiv_naturality k f₂ i]
      exact hk i))
  have hmap : pres.sheaf.obj.map k.op e₁ = pres.sheaf.obj.map k.op e₂ := hcomp
  rw [← hz, ← p.toPresheafFiber_w_apply k z pres.sheaf.obj,
    ← p.toPresheafFiber_w_apply k z pres.sheaf.obj, hmap]

/-- The map of `AlgebraicGeometry.SolutionPresentation.stalkSolution` is surjective: a solution
in the stalk ring is a tuple of germs of sections over one chart
(`Stacks.exists_toPresheafFiber_fin`) whose defining equations, holding in the stalk, hold on a
smaller chart (`AlgebraicGeometry.exists_restrict_eq_zero_of_forall_germ_eq_zero`); the
presentation then names a chart-valued point of `W` with the prescribed germs. -/
theorem surjective_stalkSolution : Function.Surjective (pres.stalkSolution p) := by
  rintro ⟨α, hα⟩
  obtain ⟨U, x, z₀, hz⟩ :=
    Stacks.exists_toPresheafFiber_fin p (P := (SmallEtale.commRingStructureSheaf B S hS).obj) α
  let z : Fin n → ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤) := z₀
  have hzg : ∀ i, smallEtaleGermHom B S hS p U x (z i) = α i := hz
  have hvanish : ∀ j, smallEtaleGermHom B S hS p U x
      (MvPolynomial.eval z (MvPolynomial.map (smallEtaleCoeff B S hS ψ U) (P j))) = 0 := by
    intro j
    rw [← MvPolynomial.eval_map_ringHom_comp (smallEtaleCoeff B S hS ψ U)
      (smallEtaleGermHom B S hS p U x) z (P j),
      smallEtaleGermHom_comp_smallEtaleCoeff B S hS p ψ U x,
      show (fun i => smallEtaleGermHom B S hS p U x (z i)) = α from funext hzg]
    exact hα j
  obtain ⟨W, k, y, hy, hk⟩ :=
    exists_restrict_eq_zero_of_forall_germ_eq_zero p
      (SmallEtale.commRingStructureSheaf B S hS).obj U x
      (fun j => MvPolynomial.eval z (MvPolynomial.map (smallEtaleCoeff B S hS ψ U) (P j)))
      hvanish
  have hsol : MvPolynomial.IsSolution P (smallEtaleCoeff B S hS ψ W)
      (fun i => smallEtaleRestrict B S hS k (z i)) := by
    intro j
    rw [← smallEtaleCoeff_comp B S hS ψ k,
      MvPolynomial.eval_map_ringHom_comp (smallEtaleCoeff B S hS ψ U)
        (smallEtaleRestrict B S hS k) z (P j)]
    exact hk j
  refine ⟨p.toPresheafFiber W y pres.sheaf.obj ((pres.equiv W).symm ⟨_, hsol⟩), ?_⟩
  refine Subtype.ext (funext fun i => ?_)
  rw [pres.stalkSolution_toPresheafFiber_coe p W y _ i, (pres.equiv W).apply_symm_apply]
  change smallEtaleGermHom B S hS p W y (smallEtaleRestrict B S hS k (z i)) = α i
  rw [smallEtaleGermHom_restrict_apply, hy]
  exact hzg i

/-- **The stalk of a solution sheaf is the solution set of the stalk.**  For a sheaf on the small
étale site of `S` presented as the solutions of a system `P` over `R` relative to
`ψ : R ⟶ Γ(S, ⊤)`, the germ map identifies the stalk at a point `p` of the site with the
solutions of `P` in the stalk ring `𝒪_{S,p}`.

This is the computation step (4) of the proof of [Stacks Project, Tag 04I6] performs on both
sides of the comparison of step (3). -/
theorem bijective_stalkSolution : Function.Bijective (pres.stalkSolution p) :=
  ⟨pres.injective_stalkSolution p, pres.surjective_stalkSolution p⟩

/-- `AlgebraicGeometry.SolutionPresentation.bijective_stalkSolution` as an equivalence. -/
def stalkSolutionEquiv :
    ToType ((p.presheafFiber (A := Type u)).obj pres.sheaf.obj) ≃
      stalkSolutionSet B S hS p ψ P :=
  Equiv.ofBijective _ (pres.bijective_stalkSolution p)

end SolutionPresentation

end AlgebraicGeometry

end
