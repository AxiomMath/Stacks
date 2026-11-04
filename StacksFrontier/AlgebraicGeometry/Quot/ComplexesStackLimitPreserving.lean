module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityReduction
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesFibreExtBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomMutualInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitDescentEq

/-!
# Limit preservation of `Complexes_{X/B}`, reduced to the results it uses

Stacks 0DLJ asserts that in Situation 0DLE, if the base `B` is locally of finite presentation
over `S`, the projection `p : Complexes_{X/B} ⥤ (Sch/S)_fppf` is limit preserving (Stacks 07XL):
for every cofiltered system of affine schemes `Tᵢ` over `S` with limit `T`, the comparison
`colim Complexes_{X/B, Tᵢ} ⥤ Complexes_{X/B, T}` is an equivalence.

The source's proof has three inputs: Stacks 05N0 (morphisms to `B` descend to a finite stage),
Stacks 0DKW (the `T`-perfect objects of `D(𝒪_{X_T})` are the colimit of the `Tᵢ`-perfect objects
of `D(𝒪_{X_{Tᵢ}})`) and Stacks 0DLC (1) (the locus where the negative self-extensions of the
fibres vanish is open), the last one finished by Stacks 05F4.  Stacks 05N0 is on the base; the
open-set case of Stacks 05F4 is Mathlib's `AlgebraicGeometry.exists_map_eq_top`.  Stacks 0DKW and
Stacks 0DLC (1) are not available unconditionally, and enter here as explicit hypotheses stated at
their content.  Nothing here is registered.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.RelativelyPerfectColimit`: **Stacks 0DKW** for the
  base changes `X_{Tᵢ}` along a cofiltered system of affine test schemes over `Y`, in the form of
  its three clauses: essential surjectivity, fullness and faithfulness of the comparison out of
  the colimit.
* `AlgebraicGeometry.Space.ComplexesSituation.FibreExtLocusIsOpen`: **Stacks 0DLC (1)** at
  `K = E` over an affine test scheme.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.descentObj`, `descentHom`, `descentEq`: the three
  stage-descent conditions of `StacksFrontier/AlgebraicGeometry/Stacks/LimitPreservingStageDescent`
  for `p`.
* `AlgebraicGeometry.Space.ComplexesSituation.fibreExtLocusIsOpen_of_existsNegativeExtLocus`:
  part (1) of Stacks 0DLC, in the shape `AlgebraicGeometry.Space.ExistsNegativeExtLocus` of
  `StacksFrontier/AlgebraicGeometry/Quot/NegativeExtLocus.lean`, gives the open used here.
* `AlgebraicGeometry.Space.ComplexesSituation.isLimitPreserving_of_existsNegativeExtLocus`:
  **Stacks 0DLJ**, granted Stacks 0DKW and Stacks 0DLC (1), in the shape the hypothesis `h0DLJ` of
  `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion` has.

## Implementation notes

*The reduction to `B`-schemes.*  By Stacks 05N0 the structure morphism of an object over the
limit factors through a stage `i`, and two such factorizations agree at a later stage
(`exists_stage_factor`, `exists_stage_eq`).  The stages over `i` then form a cofiltered system of
test schemes over `Y`, `stageDiagram`, whose limit is the vertex, `isLimitStageCone`; this is the
source's "we may assume `T = lim Tᵢ` over `B`".

*Comparisons.*  All identifications of iterated derived pullbacks are the comparisons `tri` of
the pullback datum for composites presented by equations, and their coherence is
`tri_assoc`.  Those identities are proved for test schemes and objects given as variables
(`fibre_identity₁`, `fibre_identity₂`, `comp_eq_of_fibre`) and only instantiated in the descent
proofs: the kernel compares the concrete hom-sets of derived categories structurally, and does
not finish if asked to do so at the instantiated terms.

*Isomorphisms.*  The morphisms of `Complexes_{X/B}` carry invertible comparisons, so fullness
needs an isomorphism at a finite stage; `exists_stage_iso` lifts the isomorphism and its inverse
by the fullness clause of Stacks 0DKW and makes them inverse at a later stage by its faithfulness
clause.

## References

* [Stacks Project, Tag 0DLJ](https://stacks.math.columbia.edu/tag/0DLJ)
* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 05N0](https://stacks.math.columbia.edu/tag/05N0)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

/-- The forward morphism of a composite of four isomorphisms, two of them reversed. -/
theorem CategoryTheory.Iso.trans₄_symm_hom {C : Type*} [Category C] {W X Y Z V : C}
    (e₁ : X ≅ W) (e₂ : X ≅ Y) (e₃ : Z ≅ Y) (e₄ : Z ≅ V) :
    (e₁.symm ≪≫ e₂ ≪≫ e₃.symm ≪≫ e₄).hom = e₁.inv ≫ e₂.hom ≫ e₃.inv ≫ e₄.hom :=
  rfl

/-- Cancellation of an isomorphism on the right, with the isomorphism given as a term. -/
theorem CategoryTheory.eq_of_comp_isIso {C : Type*} [Category C] {X Y Z : C} {a b : X ⟶ Y}
    {g : Y ⟶ Z} (hg : IsIso g) (h : a ≫ g = b ≫ g) : a = b := by
  obtain ⟨g', h₁, -⟩ := hg.out
  simpa only [Category.assoc, h₁, Category.comp_id] using congrArg (· ≫ g') h

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (D : ComplexesSituation B S hS)

section Triangle

variable {T₀ T₁ T₂ T₃ : SchemesOver D.Y}

/-- The comparison `L(X_c)^* ≅ L(X_b)^* ⋙ L(X_a)^*` for a morphism of test schemes presented as a
composite `a ≫ b = c`: the comparison of the pullback datum along the induced composite of base
changes. -/
def tri {a : T₀ ⟶ T₁} {b : T₁ ⟶ T₂} {c : T₀ ⟶ T₂} (h : a ≫ b = c) :
    (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c) ≅
      (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b) ⋙
        (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a) :=
  (smallEtaleDerivedPullbackData B S hS).triangle
    ((baseChangeMap_comp D.f a b).symm.trans (congrArg (fun m => D.relativeMap m) h))

/-- At the composite itself the comparison is the composition comparison. -/
theorem tri_rfl (a : T₀ ⟶ T₁) (b : T₁ ⟶ T₂) : D.tri (rfl : a ≫ b = a ≫ b) = D.compComparison a b :=
  rfl

/-- The comparison for a composite equal to `c` is the composition comparison read through the
identification of the derived pullbacks along the composite and along `c`. -/
theorem tri_eq {a : T₀ ⟶ T₁} {b : T₁ ⟶ T₂} {c : T₀ ⟶ T₂} (h : a ≫ b = c) :
    D.tri h = D.relativeMapComparison h.symm ≪≫ D.compComparison a b := by
  subst h
  have h₁ : D.relativeMapComparison (rfl : a ≫ b = a ≫ b).symm = Iso.refl _ := rfl
  rw [h₁, Iso.refl_trans]
  rfl

/-- **The associativity coherence of the comparisons**, for composites presented by equations. -/
theorem tri_assoc_iso {f : T₀ ⟶ T₁} {g : T₁ ⟶ T₂} {p : T₂ ⟶ T₃} {k : T₀ ⟶ T₂} {q : T₁ ⟶ T₃}
    {r : T₀ ⟶ T₃} (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r) :
    D.tri hkr ≪≫ Functor.isoWhiskerLeft
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap p)) (D.tri hk) =
      D.tri hr ≪≫ Functor.isoWhiskerRight (D.tri hq)
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap f)) ≪≫
        Functor.associator ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap p))
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap g))
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap f)) :=
  (smallEtaleDerivedPullbackData_isCoherent B S hS).triangle_comp _ _ _ _

/-- **The associativity coherence of the comparisons**, at an object. -/
theorem tri_assoc {f : T₀ ⟶ T₁} {g : T₁ ⟶ T₂} {p : T₂ ⟶ T₃} {k : T₀ ⟶ T₂} {q : T₁ ⟶ T₃}
    {r : T₀ ⟶ T₃} (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r)
    (M : derivedModules B S hS (D.space T₃)) :
    (D.tri hkr).hom.app M ≫ (D.tri hk).hom.app
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap p)).obj M) =
      (D.tri hr).hom.app M ≫ ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap f)).map ((D.tri hq).hom.app M) := by
  have := congrArg (fun e => e.hom.app M) (D.tri_assoc_iso hk hq hr hkr)
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app] at this
  rw [this, Category.comp_id]

/-- The derived pullback of a morphism along a composite, read through the comparison. -/
theorem pull_map_tri {a : T₀ ⟶ T₁} {b : T₁ ⟶ T₂} {c : T₀ ⟶ T₂} (h : a ≫ b = c)
    {M N : derivedModules B S hS (D.space T₂)} (α : M ⟶ N) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).map α =
      (D.tri h).hom.app M ≫ ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).map
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).map α) ≫
          (D.tri h).inv.app N := by
  rw [← Functor.comp_map, ← NatTrans.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- Equality of derived pullbacks of two morphisms along a composite follows from equality along
its last factor. -/
theorem pull_map_eq_of_tri {a : T₀ ⟶ T₁} {b : T₁ ⟶ T₂} {c : T₀ ⟶ T₂} (h : a ≫ b = c)
    {M N : derivedModules B S hS (D.space T₂)} {α β : M ⟶ N}
    (e : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).map α =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).map β) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).map α =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).map β := by
  rw [D.pull_map_tri h α, D.pull_map_tri h β, e]

/-- Equality of derived pullbacks of two morphisms along a composite follows from equality of the
iterated derived pullbacks. -/
theorem pull_map_eq_of_tri'' {a : T₀ ⟶ T₁} {b : T₁ ⟶ T₂} {c : T₀ ⟶ T₂} (h : a ≫ b = c)
    {M N : derivedModules B S hS (D.space T₂)} {α β : M ⟶ N}
    (e : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).map
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).map α) =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).map
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).map β)) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).map α =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).map β := by
  rw [D.pull_map_tri h α, D.pull_map_tri h β, e]

/-- Equality of derived pullbacks of two morphisms along the last factor of a composite follows
from equality along the composite. -/
theorem pull_map_eq_of_tri' {a : T₀ ⟶ T₁} {b : T₁ ⟶ T₂} {c : T₀ ⟶ T₂} (h : a ≫ b = c)
    {M N : derivedModules B S hS (D.space T₂)} {α β : M ⟶ N}
    (e : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).map α =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).map β) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).map
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).map α) =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).map
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).map β) := by
  rw [D.pull_map_tri h α, D.pull_map_tri h β, cancel_epi] at e
  exact (((D.tri h).app N).cancel_iso_inv_right _ _).1 e

end Triangle

/-- The identification of the derived pullback to the cone point of an object pulled back along
a transition morphism with its derived pullback along the cone projection: the inverse of the
comparison for the composite `d.π k ≫ F.map s = d.π i`. -/
def coneStageComparison {I : Type*} [Category I] {F : I ⥤ SchemesOver D.Y} (d : Cone F)
    {k i : I} (s : k ⟶ i) (E : derivedModules B S hS (D.space (F.obj i))) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app k))).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).obj E) ≅
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).obj E :=
  ((D.tri (d.w s)).app E).symm

section Transfer

variable {I : Type*} [Category I] {F : I ⥤ SchemesOver D.Y} (d : Cone F)

/-- A morphism between the pullbacks of two objects of a stage `o` along a transition `t : k ⟶ o`,
carried to the cone point: its derived pullback along the projection from the cone point to `k`,
conjugated by the comparison for `d.π k ≫ F.map t = d.π o`. -/
abbrev conjAt {k o : I} (t : k ⟶ o) {E E' : derivedModules B S hS (D.space (F.obj o))}
    (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj E ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj E') :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app o))).obj E ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app o))).obj E' :=
  Functor.conjHom (D.tri (d.w t)) ψ

variable (F) in
/-- A morphism between the pullbacks of two objects of a stage `o` along `t : k ⟶ o`, carried to a
later stage `t' = u ≫ t` by derived pullback along `F.map u`. -/
abbrev transfer {k k' o : I} {t : k ⟶ o} {u : k' ⟶ k} {t' : k' ⟶ o} (h : u ≫ t = t')
    {E E' : derivedModules B S hS (D.space (F.obj o))}
    (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj E ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj E') :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t'))).obj E ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t'))).obj E' :=
  Functor.conjHom (D.tri ((F.map_comp u t).symm.trans (congrArg F.map h))) ψ

/-- **Carrying a morphism to a later stage does not change its image at the cone point.** -/
theorem conjAt_transfer {k k' o : I} {t : k ⟶ o} {u : k' ⟶ k} {t' : k' ⟶ o} (h : u ≫ t = t')
    {E E' : derivedModules B S hS (D.space (F.obj o))}
    (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj E ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj E') :
    D.conjAt d t' (D.transfer F h ψ) = D.conjAt d t ψ :=
  (Functor.conjHom_comp (D.tri ((F.map_comp u t).symm.trans (congrArg F.map h)))
    (D.tri (d.w t')) (D.tri (d.w t)) (D.tri (d.w u))
    ((smallEtaleDerivedPullbackData_isCoherent B S hS).triangle_comp' _ _ _ _) ψ).symm

/-- Two morphisms whose derived pullbacks along `F.map u` agree are carried to the same
morphism. -/
theorem transfer_eq_of_pull_map_eq {k k' o : I} {t : k ⟶ o} {u : k' ⟶ k} {t' : k' ⟶ o}
    (h : u ≫ t = t') {E E' : derivedModules B S hS (D.space (F.obj o))}
    {ψ χ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj E ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj E'}
    (e : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map u))).map ψ =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map u))).map χ) :
    D.transfer F h ψ = D.transfer F h χ := by
  rw [transfer, transfer, Functor.conjHom, Functor.conjHom, e]

/-- **Isomorphisms descend**, from the clauses of Stacks 0DKW on morphisms: an isomorphism at the
cone point between the pullbacks of two relatively perfect objects of a stage is, at a later
stage, the image of an isomorphism. -/
theorem exists_stage_iso [IsCofiltered I]
    (hhom : ∀ (i : I) (E E' : derivedModules B S hS (D.space (F.obj i))),
      D.IsRelativelyPerfect (F.obj i) E → D.IsRelativelyPerfect (F.obj i) E' →
      ∀ φ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).obj E ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).obj E',
      ∃ (k : I) (s : k ⟶ i)
        (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).obj E ⟶
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).obj E'),
        φ = D.conjAt d s ψ)
    (heq : ∀ (i : I) (E E' : derivedModules B S hS (D.space (F.obj i))),
      D.IsRelativelyPerfect (F.obj i) E → D.IsRelativelyPerfect (F.obj i) E' →
      ∀ ψ ψ' : E ⟶ E',
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).map ψ =
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).map ψ' →
        ∃ (k : I) (s : k ⟶ i),
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).map ψ =
            ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).map ψ')
    {o : I} {E E' : derivedModules B S hS (D.space (F.obj o))}
    (hE : D.IsRelativelyPerfect (F.obj o) E) (hE' : D.IsRelativelyPerfect (F.obj o) E')
    (Φ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app o))).obj E ≅
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app o))).obj E') :
    ∃ (k : I) (t : k ⟶ o)
      (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj E ≅
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj E'),
      Φ.hom = D.conjAt d t ψ.hom := by
  obtain ⟨k₁, t₁, ψ₁, h₁⟩ := hhom o E E' hE hE' Φ.hom
  obtain ⟨k₂, t₂, χ₂, h₂⟩ := hhom o E' E hE' hE Φ.inv
  obtain ⟨k₃, u₁, u₂, hu⟩ := IsCofiltered.cospan t₁ t₂
  let ψ₃ := D.transfer F (rfl : u₁ ≫ t₁ = u₁ ≫ t₁) ψ₁
  let χ₃ := D.transfer F hu.symm χ₂
  have c₁ : D.conjAt d (u₁ ≫ t₁) ψ₃ = Φ.hom := (D.conjAt_transfer d _ ψ₁).trans h₁.symm
  have c₂ : D.conjAt d (u₁ ≫ t₁) χ₃ = Φ.inv := (D.conjAt_transfer d _ χ₂).trans h₂.symm
  have hE₃ := D.relativelyPerfectBaseChange (F.map (u₁ ≫ t₁)) E hE
  have hE₃' := D.relativelyPerfectBaseChange (F.map (u₁ ≫ t₁)) E' hE'
  have e₁ := Functor.map_eq_of_conjHom_eq (D.tri (d.w (u₁ ≫ t₁))) _ _
    (((Functor.conjHom_comp_morphism _ ψ₃ χ₃).trans ((congrArg₂ (· ≫ ·) c₁ c₂).trans
      Φ.hom_inv_id)).trans
      (Functor.conjHom_id_morphism _ E).symm)
  have e₂ := Functor.map_eq_of_conjHom_eq (D.tri (d.w (u₁ ≫ t₁))) _ _
    (((Functor.conjHom_comp_morphism _ χ₃ ψ₃).trans ((congrArg₂ (· ≫ ·) c₂ c₁).trans
      Φ.inv_hom_id)).trans
      (Functor.conjHom_id_morphism _ E').symm)
  obtain ⟨k₄, u₄, e₄⟩ := heq k₃ _ _ hE₃ hE₃ _ _ e₁
  obtain ⟨k₅, u₅, e₅⟩ := heq k₃ _ _ hE₃' hE₃' _ _ e₂
  obtain ⟨k₆, v₄, v₅, hv⟩ := IsCofiltered.cospan u₄ u₅
  let ψ₆ := D.transfer F (rfl : (v₄ ≫ u₄) ≫ u₁ ≫ t₁ = (v₄ ≫ u₄) ≫ u₁ ≫ t₁) ψ₃
  let χ₆ := D.transfer F (rfl : (v₄ ≫ u₄) ≫ u₁ ≫ t₁ = (v₄ ≫ u₄) ≫ u₁ ≫ t₁) χ₃
  have i₁ : ψ₆ ≫ χ₆ = 𝟙 _ :=
    ((Functor.conjHom_comp_morphism _ ψ₃ χ₃).symm.trans (D.transfer_eq_of_pull_map_eq
      (rfl : (v₄ ≫ u₄) ≫ u₁ ≫ t₁ = (v₄ ≫ u₄) ≫ u₁ ≫ t₁)
      (D.pull_map_eq_of_tri (F.map_comp v₄ u₄).symm e₄))).trans
        (Functor.conjHom_id_morphism _ E)
  have i₂ : χ₆ ≫ ψ₆ = 𝟙 _ := by
    have e₅' := D.pull_map_eq_of_tri (F.map_comp v₅ u₅).symm e₅
    rw [← hv] at e₅'
    exact ((Functor.conjHom_comp_morphism _ χ₃ ψ₃).symm.trans
      (D.transfer_eq_of_pull_map_eq (rfl : (v₄ ≫ u₄) ≫ u₁ ≫ t₁ = (v₄ ≫ u₄) ≫ u₁ ≫ t₁)
        e₅')).trans (Functor.conjHom_id_morphism _ E')
  exact ⟨k₆, (v₄ ≫ u₄) ≫ u₁ ≫ t₁, ⟨ψ₆, χ₆, i₁, i₂⟩,
    ((D.conjAt_transfer d (rfl : (v₄ ≫ u₄) ≫ u₁ ≫ t₁ = (v₄ ≫ u₄) ≫ u₁ ≫ t₁) ψ₃).trans c₁).symm⟩

end Transfer

/-- **Stacks 0DKW, not yet proved here.**  In Situation 0DLE, for every cofiltered
system `F` of affine test schemes over `Y` and every cone `d` over it whose vertex is affine and
whose underlying schemes form a limit, the category of `d.pt`-perfect objects of
`D(𝒪_{X_{d.pt}})` is the colimit of the categories of `F i`-perfect objects of `D(𝒪_{X_{F i}})`
along derived pullback: every relatively perfect object at the vertex is the pullback of one at
a stage; every morphism at the vertex between pullbacks of relatively perfect objects of a stage
comes from a morphism at a later stage; and two morphisms of a stage which agree at the vertex
agree at a later stage. -/
def RelativelyPerfectColimit : Prop :=
  ∀ (I : Type u) [Category.{u} I] [IsCofiltered I] (F : I ⥤ SchemesOver D.Y) (d : Cone F),
    IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone d) →
    (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (F.obj i).left)) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj d.pt.left) →
    (∀ E : derivedModules B S hS (D.space d.pt), D.IsRelativelyPerfect d.pt E →
      ∃ (i : I) (Ei : derivedModules B S hS (D.space (F.obj i))),
        D.IsRelativelyPerfect (F.obj i) Ei ∧
        Nonempty (((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (d.π.app i))).obj Ei ≅ E)) ∧
    (∀ (i : I) (E E' : derivedModules B S hS (D.space (F.obj i))),
      D.IsRelativelyPerfect (F.obj i) E → D.IsRelativelyPerfect (F.obj i) E' →
      ∀ φ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).obj E ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).obj E',
      ∃ (k : I) (s : k ⟶ i)
        (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).obj E ⟶
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).obj E'),
        φ = D.conjAt d s ψ) ∧
    (∀ (i : I) (E E' : derivedModules B S hS (D.space (F.obj i))),
      D.IsRelativelyPerfect (F.obj i) E → D.IsRelativelyPerfect (F.obj i) E' →
      ∀ ψ ψ' : E ⟶ E',
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).map ψ =
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).map ψ' →
        ∃ (k : I) (s : k ⟶ i),
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).map ψ =
            ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).map ψ')

/-- **Stacks 0DLC (1) at `K = E`, over an affine test scheme** (Stacks 0DLC is pending on Stacks
0DKY, not yet proved here): for a relatively perfect `E` on `X_T`, there is an open `W ⊆ T` such
that a point `y : T₀ ⟶ T` with values in a field lands in `W` exactly when the negative
self-extensions of the derived pullback of `E` to the fibre `X_y` vanish. -/
def FibreExtLocusIsOpen : Prop :=
  ∀ (T : SchemesOver D.Y) (E : derivedModules B S hS (D.space T)),
    IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) → D.IsRelativelyPerfect T E →
    ∃ W : ((BigFppfOver.toScheme B S hS).obj T.left).Opens,
      ∀ (T₀ : SchemesOver D.Y), Stack.IsFieldObject B S hS T₀.left → ∀ y : T₀ ⟶ T,
        (Set.range ((BigFppfOver.toScheme B S hS).map y.left).base ⊆ W ↔
          ∀ i : ℤ, i < 0 →
            Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj E ⟶
              (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj E)⟦i⟧))

section FibreIdentities

variable {T₀ T₁ T₂ T₃ T₄ : SchemesOver D.Y}

/-- The comparison identity behind `δₖ ≫ dₓ = δ` in the descent of morphisms. -/
theorem fibre_identity₁ {f : T₀ ⟶ T₁} {g : T₁ ⟶ T₂} {p : T₂ ⟶ T₃} {k : T₀ ⟶ T₂}
    {q : T₁ ⟶ T₃} {r : T₀ ⟶ T₃} (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r)
    (hkr : k ≫ p = r) (M : derivedModules B S hS (D.space T₃))
    {X : derivedModules B S hS (D.space T₀)} (a : ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap r)).obj M ⟶ X) :
    Functor.fibreComp (D.tri hr) ((D.tri hk).inv.app
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap p)).obj M) ≫
      (D.tri hkr).inv.app M ≫ a) ((D.tri hq).hom.app M) = a := by
  rw [Functor.fibreComp, ← Category.assoc, ← D.tri_assoc hk hq hr hkr M, Category.assoc,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

/-- The comparison identity behind `δₖ ≫ ψ ≫ d_y = φ ≫ ε` in the descent of morphisms. -/
theorem fibre_identity₂ {f : T₀ ⟶ T₁} {g : T₁ ⟶ T₂} {k : T₀ ⟶ T₂} (hk : f ≫ g = k)
    {mx : T₂ ⟶ T₃} {my : T₂ ⟶ T₄} {bδ : T₀ ⟶ T₃} {bε : T₀ ⟶ T₄} (hδm : k ≫ mx = bδ)
    (hεm : k ≫ my = bε) {qy : T₁ ⟶ T₄} (hq : g ≫ my = qy) (hb : f ≫ qy = bε)
    {xiE : derivedModules B S hS (D.space T₃)} {yiE : derivedModules B S hS (D.space T₄)}
    {xE : derivedModules B S hS (D.space T₀)} (fδ : ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap bδ)).obj xiE ⟶ xE)
    (gδ : xE ⟶ ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap bδ)).obj xiE)
        (hgδ : gδ ≫ fδ = 𝟙 xE)
    (fε : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap bε)).obj yiE ⟶ xE)
    (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap g)).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap my)).obj yiE) ⟶
            ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap g)).obj
                (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap mx)).obj xiE))
    (hΦ : Functor.conjHom (D.tri hk) ψ =
      (D.tri hεm).inv.app yiE ≫ fε ≫ gδ ≫ (D.tri hδm).hom.app xiE) :
    Functor.fibreComp (D.tri hb) ((D.tri hk).inv.app
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap mx)).obj xiE) ≫
      (D.tri hδm).inv.app xiE ≫ fδ) ((D.tri hq).hom.app yiE ≫ ψ) = fε := by
  have a := D.tri_assoc hk hq hb hεm yiE
  rw [Functor.conjHom] at hΦ
  rw [Functor.fibreComp, Functor.map_comp]
  calc _ = ((D.tri hb).hom.app yiE ≫ ((smallEtaleDerivedPullbackData B S hS).pull
      (D.relativeMap f)).map ((D.tri hq).hom.app yiE)) ≫
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap f)).map ψ ≫
            (D.tri hk).inv.app (((smallEtaleDerivedPullbackData B S hS).pull
                (D.relativeMap mx)).obj xiE) ≫
          (D.tri hδm).inv.app xiE ≫ fδ := by simp only [Category.assoc]
    _ = ((D.tri hεm).hom.app yiE ≫ (D.tri hk).hom.app
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap my)).obj yiE)) ≫
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap f)).map ψ ≫
            (D.tri hk).inv.app (((smallEtaleDerivedPullbackData B S hS).pull
                (D.relativeMap mx)).obj xiE) ≫
          (D.tri hδm).inv.app xiE ≫ fδ := by rw [a]
    _ = (D.tri hεm).hom.app yiE ≫ ((D.tri hk).hom.app
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap my)).obj yiE) ≫
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap f)).map ψ ≫
            (D.tri hk).inv.app (((smallEtaleDerivedPullbackData B S hS).pull
                (D.relativeMap mx)).obj xiE)) ≫
          (D.tri hδm).inv.app xiE ≫ fδ := by simp only [Category.assoc]
    _ = fε := by
      rw [hΦ, Category.assoc, Iso.hom_inv_id_app_assoc, Category.assoc, Category.assoc,
        Iso.hom_inv_id_app_assoc, hgδ, Category.comp_id]

/-- The component at an object of the comparison for a composite, with the iterated pullback
written out. -/
abbrev triApp {a : T₀ ⟶ T₁} {b : T₁ ⟶ T₂} {c : T₀ ⟶ T₂} (h : a ≫ b = c)
    (M : derivedModules B S hS (D.space T₂)) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).obj M ≅
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).obj
            (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj M) :=
  (D.tri h).app M

/-- `AlgebraicGeometry.Space.ComplexesSituation.fibre_identity₁` through
`AlgebraicGeometry.Space.ComplexesSituation.triApp`. -/
theorem fibre_identity₁' {f : T₀ ⟶ T₁} {g : T₁ ⟶ T₂} {p : T₂ ⟶ T₃} {k : T₀ ⟶ T₂}
    {q : T₁ ⟶ T₃} {r : T₀ ⟶ T₃} (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r)
    (hkr : k ≫ p = r) (M : derivedModules B S hS (D.space T₃))
    {X : derivedModules B S hS (D.space T₀)} (a : ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap r)).obj M ⟶ X) :
    Functor.fibreComp (D.tri hr) ((D.triApp hk (((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap p)).obj M)).inv ≫ (D.triApp hkr M).inv ≫ a)
      (D.triApp hq M).hom = a :=
  D.fibre_identity₁ hk hq hr hkr M a

/-- `AlgebraicGeometry.Space.ComplexesSituation.fibre_identity₂` through
`AlgebraicGeometry.Space.ComplexesSituation.triApp`. -/
theorem fibre_identity₂' {f : T₀ ⟶ T₁} {g : T₁ ⟶ T₂} {k : T₀ ⟶ T₂} (hk : f ≫ g = k)
    {mx : T₂ ⟶ T₃} {my : T₂ ⟶ T₄} {bδ : T₀ ⟶ T₃} {bε : T₀ ⟶ T₄} (hδm : k ≫ mx = bδ)
    (hεm : k ≫ my = bε) {qy : T₁ ⟶ T₄} (hq : g ≫ my = qy) (hb : f ≫ qy = bε)
    {xiE : derivedModules B S hS (D.space T₃)} {yiE : derivedModules B S hS (D.space T₄)}
    {xE : derivedModules B S hS (D.space T₀)} (fδ : ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap bδ)).obj xiE ⟶ xE)
    (gδ : xE ⟶ ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap bδ)).obj xiE)
        (hgδ : gδ ≫ fδ = 𝟙 xE) (fε : ((smallEtaleDerivedPullbackData B S hS).pull
            (D.relativeMap bε)).obj yiE ⟶ xE)
    (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap g)).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap my)).obj yiE) ⟶
            ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap g)).obj
                (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap mx)).obj xiE))
    (hΦ : Functor.conjHom (D.tri hk) ψ =
      (D.triApp hεm yiE).inv ≫ fε ≫ gδ ≫ (D.triApp hδm xiE).hom) :
    Functor.fibreComp (D.tri hb) ((D.triApp hk (((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap mx)).obj xiE)).inv ≫
      (D.triApp hδm xiE).inv ≫ fδ) ((D.triApp hq yiE).hom ≫ ψ) = fε :=
  D.fibre_identity₂ hk hδm hεm hq hb fδ gδ hgδ fε ψ hΦ

end FibreIdentities

section Stage

variable {I : Type u} [Category.{u} I] (Dg : I ⥤ BigAffineFppf B S hS)

/-- The diagram of the stages `j ⟶ i` of an inverse system of affine schemes, made schemes over
`Y` through a morphism from the `i`-th stage to `Y`. -/
@[simps]
def stageDiagram (i : I)
    (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (Dg.obj i)) ⟶
      D.Y) : Over i ⥤ SchemesOver D.Y where
  obj j := CostructuredArrow.mk
    ((schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (Dg.map j.hom)) ≫ g)
  map {j j'} f := CostructuredArrow.homMk
    ((BigAffineFppf.inclusion B S hS).map (Dg.map f.left)) (by
      dsimp
      rw [← Functor.map_comp_assoc]
      change (schemeSpaceFunctor B S hS).map ((Dg.map f.left ≫ Dg.map j'.hom).hom) ≫ g = _
      rw [← Dg.map_comp, Over.w f])
  map_id j := CostructuredArrow.hom_ext _ _ (by simp)
  map_comp f f' := CostructuredArrow.hom_ext _ _ (by simp)

variable (c : Cone Dg)

/-- The cone over `AlgebraicGeometry.Space.ComplexesSituation.stageDiagram` with vertex a scheme
`A` over `Y` whose underlying scheme is the vertex of `c` and whose morphism to `Y` factors
through the `i`-th stage. -/
@[simps]
def stageCone (i : I)
    (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (Dg.obj i)) ⟶
      D.Y) (A : SchemesOver D.Y) (hA : A.left = (BigAffineFppf.inclusion B S hS).obj c.pt)
    (hg : A.hom = (schemeSpaceFunctor B S hS).map
      (eqToHom hA ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ g) :
    Cone (D.stageDiagram Dg i g) where
  pt := A
  π :=
    { app j := CostructuredArrow.homMk (f := A) (f' := (D.stageDiagram Dg i g).obj j)
        (eqToHom hA ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app j.left)) (by
          change (schemeSpaceFunctor B S hS).map
              (eqToHom hA ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app j.left)) ≫
            ((schemeSpaceFunctor B S hS).map
              ((BigAffineFppf.inclusion B S hS).map (Dg.map j.hom)) ≫ g) = A.hom
          rw [hg, ← Category.assoc, ← Functor.map_comp, Category.assoc, ← Functor.map_comp,
            c.w j.hom])
      naturality j j' f := CostructuredArrow.hom_ext _ _ (by
        change 𝟙 A.left ≫ eqToHom hA ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app j'.left) =
          (eqToHom hA ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app j.left)) ≫
            (BigAffineFppf.inclusion B S hS).map (Dg.map f.left)
        rw [Category.id_comp, Category.assoc, ← Functor.map_comp, c.w f.left]) }

variable {c} in
/-- The vertex of `AlgebraicGeometry.Space.ComplexesSituation.stageCone` is a limit of the
underlying schemes, the stages over `i` being initial in a cofiltered system. -/
def isLimitStageCone [IsCofiltered I]
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I)
    (g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (Dg.obj i)) ⟶
      D.Y) (A : SchemesOver D.Y) (hA : A.left = (BigAffineFppf.inclusion B S hS).obj c.pt)
    (hg : A.hom = (schemeSpaceFunctor B S hS).map
      (eqToHom hA ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ g) :
    IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone (D.stageCone Dg c i g A hA hg)) :=
  let h₁ : IsLimit (((BigAffineFppf.toScheme B S hS).mapCone c).whisker (Over.forget i)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) _).symm hc
  let c₂ : Cone (Over.forget i ⋙ Dg ⋙ BigAffineFppf.toScheme B S hS) :=
    (CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone (D.stageCone Dg c i g A hA hg)
  h₁.ofIsoLimit (Cones.ext (c' := c₂)
    ((BigFppfOver.toScheme B S hS).mapIso (eqToIso hA.symm)) (fun j => by
      change (BigFppfOver.toScheme B S hS).map
          ((BigAffineFppf.inclusion B S hS).map (c.π.app j.left)) =
        (BigFppfOver.toScheme B S hS).map (eqToHom hA.symm) ≫
          (BigFppfOver.toScheme B S hS).map
            (eqToHom hA ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app j.left))
      rw [← Functor.map_comp, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]))

end Stage

section FunctorOfPoints

variable {D} {I : Type u} [Category.{u} I] [IsCofiltered I] {Dg : I ⥤ BigAffineFppf B S hS}
  {c : Cone Dg}

omit [IsCofiltered I] in
/-- The element of `Y(U)` of a composite `U ⟶ V ⟶ Y` is the restriction of that of `V ⟶ Y`. -/
theorem yonedaEquiv_map_comp {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (g : (schemeSpaceFunctor B S hS).obj V ⟶ D.Y) :
    yonedaEquiv (X := U) (F := D.Y.1) ((schemeSpaceFunctor B S hS).map f ≫ g).hom =
      D.Y.1.map f.op (yonedaEquiv (X := V) (F := D.Y.1) g.hom) :=
  (yonedaEquiv_naturality (X := V) (F := D.Y.1) g.hom f).symm

omit [IsCofiltered I] in
/-- Two morphisms to `Y` are equal as soon as their elements of the functor of points are. -/
theorem hom_ext_yonedaEquiv {U : BigFppfOver B S hS}
    {g g' : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y}
    (h : yonedaEquiv (X := U) (F := D.Y.1) g.hom = yonedaEquiv (X := U) (F := D.Y.1) g'.hom) :
    g = g' :=
  ObjectProperty.hom_ext _ (yonedaEquiv.injective h)

/-- **Stacks 05N0 at an inverse system of affine schemes.**  If `Y` is locally of finite
presentation over `S`, then `Y(lim Tᵢ) = colim Y(Tᵢ)`. -/
theorem nonempty_isColimit_mapCocone_Y
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Nonempty (IsColimit (D.Y.1.mapCocone ((BigAffineFppf.inclusion B S hS).mapCone c).op)) :=
  (isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS D.Y.2).1 hY I
    (Dg ⋙ BigAffineFppf.inclusion B S hS) _ hc (fun i => (Dg.obj i).2) c.pt.2

/-- A morphism from the vertex of the system to `Y` factors through a stage. -/
theorem exists_stage_factor (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (U : BigFppfOver B S hS)
    (hU : U = (BigAffineFppf.inclusion B S hS).obj c.pt)
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y) :
    ∃ (i : I) (g : (schemeSpaceFunctor B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (Dg.obj i)) ⟶ D.Y),
      h = (schemeSpaceFunctor B S hS).map
        (eqToHom hU ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ g := by
  obtain ⟨hcol⟩ := nonempty_isColimit_mapCocone_Y hY hc
  subst hU
  obtain ⟨j, v, hv⟩ := Types.jointly_surjective_of_isColimit hcol
    (yonedaEquiv (X := (BigAffineFppf.inclusion B S hS).obj c.pt) (F := D.Y.1) h.hom)
  refine ⟨j.unop, ObjectProperty.homMk (yonedaEquiv.symm v), hom_ext_yonedaEquiv ?_⟩
  rw [yonedaEquiv_map_comp, eqToHom_refl]
  refine hv.symm.trans ?_
  show D.Y.1.map ((BigAffineFppf.inclusion B S hS).map (c.π.app j.unop)).op v =
    D.Y.1.map (𝟙 _ ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app j.unop)).op
      (yonedaEquiv (yonedaEquiv.symm v))
  rw [Equiv.apply_symm_apply, Category.id_comp]

/-- Two morphisms from a stage to `Y` which agree on the vertex of the system agree on a later
stage. -/
theorem exists_stage_eq (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I)
    (g g' : (schemeSpaceFunctor B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (Dg.obj i)) ⟶ D.Y)
    (h : (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ g =
      (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ g') :
    ∃ (k : I) (s : k ⟶ i),
      (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (Dg.map s)) ≫ g =
        (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (Dg.map s)) ≫ g' := by
  obtain ⟨hcol⟩ := nonempty_isColimit_mapCocone_Y hY hc
  have h' := congrArg (fun m => yonedaEquiv (F := D.Y.1) m.hom) h
  simp only [yonedaEquiv_map_comp] at h'
  obtain ⟨k, f, f', hk⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff _ hcol (i := op i) (j := op i)).1 h'
  refine ⟨IsCofiltered.eq f.unop f'.unop, IsCofiltered.eqHom f.unop f'.unop ≫ f.unop,
    hom_ext_yonedaEquiv ?_⟩
  rw [yonedaEquiv_map_comp, yonedaEquiv_map_comp]
  conv_rhs => rw [IsCofiltered.eq_condition]
  simp only [Functor.map_comp, op_comp]
  exact congrArg _ hk

end FunctorOfPoints

section FibreExt

/-- The vanishing of a negative self-extension on a fibre transports along an isomorphism of
complexes and along the composition comparison. -/
theorem subsingleton_fibreExt_comp_iff {T₀ T T' : SchemesOver D.Y} (y : T₀ ⟶ T) (h : T ⟶ T')
    (E : derivedModules B S hS (D.space T')) (i : ℤ) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E) ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E))⟦i⟧) ↔
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (y ≫ h))).obj E ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (y ≫ h))).obj E)⟦i⟧) :=
  ⟨subsingleton_hom_shift_of_iso ((D.compComparison y h).app E).symm i,
    subsingleton_hom_shift_of_iso ((D.compComparison y h).app E) i⟩

/-- The vanishing of a negative self-extension on a fibre transports along an isomorphism of
complexes. -/
theorem subsingleton_fibreExt_iso_iff {T₀ T : SchemesOver D.Y} (y : T₀ ⟶ T)
    {E E' : derivedModules B S hS (D.space T)} (e : E ≅ E') (i : ℤ) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj E ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj E)⟦i⟧) ↔
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj E' ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj E')⟦i⟧) :=
  ⟨subsingleton_hom_shift_of_iso
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).mapIso e) i,
    subsingleton_hom_shift_of_iso
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).mapIso e.symm) i⟩

/-- Every point of a test scheme over `Y` is the image of a point with values in a field, its
residue field. -/
theorem exists_fieldPoint (T : SchemesOver D.Y) (t : (BigFppfOver.toScheme B S hS).obj T.left) :
    ∃ (T₀ : SchemesOver D.Y) (y : T₀ ⟶ T), Stack.IsFieldObject B S hS T₀.left ∧
      t ∈ Set.range ((BigFppfOver.toScheme B S hS).map y.left).base := by
  let X := (BigFppfOver.toScheme B S hS).obj T.left
  have hl : B.Contains (Spec (.of (X.residueField t))) :=
    B.residueField_spec_contains T.left.left.2 t
  let ρ : B.obj hl ⟶ T.left.left := ObjectProperty.homMk (X.fromSpecResidueField t)
  let U : BigFppfOver B S hS := Over.mk (ρ ≫ T.left.hom)
  let v : U ⟶ T.left := Over.homMk ρ rfl
  let T₀ : SchemesOver D.Y := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map v ≫ T.hom)
  exact ⟨T₀, CostructuredArrow.homMk v rfl, ⟨X.residueField t, inferInstance, ⟨Iso.refl _⟩⟩,
    IsLocalRing.closedPoint _, X.fromSpecResidueField_apply t _⟩

end FibreExt

section Bridge

/-- **An open subspace of a scheme is an open of the scheme**: a morphism `a : Z ⟶ A` of the site
is a section over `Z` of an open subspace `W` of `A` exactly when it lands in the open of `A`
which represents `W`. -/
theorem exists_opens_mem_iff {A : BigFppfOver B S hS} (W : OpenSubspaces B S hS (yoneda.obj A)) :
    ∃ U : ((BigFppfOver.toScheme B S hS).obj A).Opens, ∀ (Z : BigFppfOver B S hS) (a : Z ⟶ A),
      a ∈ W.1.obj (op Z) ↔ Set.range ((BigFppfOver.toScheme B S hS).map a) ⊆ U := by
  have hW := W.2.2
  let hrep := hW.rep
  let j := hrep.snd (𝟙 (yoneda.obj A))
  have hj : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) :=
    hW.property_snd (𝟙 _)
  have hpb := hrep.isPullback (𝟙 (yoneda.obj A))
  refine ⟨((BigFppfOver.toScheme B S hS).map j).opensRange, fun Z a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · let x : W.1.toFunctor.obj (op Z) := ⟨a, ha⟩
    let w : yoneda.obj Z ⟶ W.1.toFunctor := yonedaEquiv.symm x
    have hw : w ≫ W.1.ι = yoneda.map a := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      show W.1.ι.app _ (yonedaEquiv (yonedaEquiv.symm x)) = a
      rw [Equiv.apply_symm_apply]
      rfl
    let l := hpb.lift w (yoneda.map a) (by rw [hw, Category.comp_id])
    have hl : l ≫ yoneda.map j = yoneda.map a := hpb.lift_snd _ _ _
    obtain ⟨l', hl'⟩ := yoneda.map_surjective l
    rw [← hl', ← yoneda.map_comp] at hl
    rw [← yoneda.map_injective hl, Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp]
    exact Set.image_subset_range _ _
  · let lift := AlgebraicGeometry.IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map j)
      ((BigFppfOver.toScheme B S hS).map a) (by simpa [Scheme.Hom.coe_opensRange] using ha)
    have hlift : lift ≫ (BigFppfOver.toScheme B S hS).map j = (BigFppfOver.toScheme B S hS).map a :=
      AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
    let l' : Z ⟶ hrep.pullback (𝟙 (yoneda.obj A)) :=
      Over.homMk (ObjectProperty.homMk lift) (by
        apply B.inclusion.map_injective
        have h₁ := congrArg B.inclusion.map (Over.w j)
        have h₂ := congrArg B.inclusion.map (Over.w a)
        simp only [Functor.map_comp] at h₁ h₂ ⊢
        show lift ≫ _ = _
        rw [← h₁, ← Category.assoc]
        exact (congrArg (· ≫ _) hlift).trans h₂)
    have hl' : l' ≫ j = a := (BigFppfOver.toScheme B S hS).map_injective hlift
    have e : ((hrep.fst (𝟙 (yoneda.obj A))).app (op Z) l').1 = a := by
      have h := congrArg (fun m => m.app (op Z) l') hpb.w
      exact (by simpa using h : _ = l' ≫ j).trans hl'
    exact e ▸ ((hrep.fst (𝟙 (yoneda.obj A))).app (op Z) l').2

/-- The vanishing of a negative self-extension on a fibre does not depend on the model of the
fibre. -/
theorem subsingleton_baseChangeProjection_iff {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (E : derivedModules B S hS X) {T₀ : SchemesOver Y} {Z : AlgebraicSpaces B S hS}
    {p : Z ⟶ X} {q : Z ⟶ (schemeSpaceFunctor B S hS).obj T₀.left}
    (hpb : IsPullback p q f T₀.hom) (i : ℤ) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull
        (baseChangeProjection f T₀)).obj E ⟶ (((smallEtaleDerivedPullbackData B S hS).pull
          (baseChangeProjection f T₀)).obj E)⟦i⟧) ↔
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull p).obj E ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull p).obj E)⟦i⟧) := by
  let P := smallEtaleDerivedPullbackData B S hS
  have hT : IsPullback (baseChangeProjection f T₀) (baseChangeInclusion f T₀) f T₀.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f T₀.hom
  let φ : Z ≅ baseChangeSpace f T₀ := hpb.isoIsPullback _ _ hT
  have hφ : φ.hom ≫ baseChangeProjection f T₀ = p := hpb.isoIsPullback_hom_fst _ _ hT
  have hφ' : φ.inv ≫ p = baseChangeProjection f T₀ := by rw [← hφ, Iso.inv_hom_id_assoc]
  exact ⟨fun h => subsingleton_hom_shift_of_iso ((P.triangle hφ).app E).symm i
      (subsingleton_hom_shift_pull_of_iso φ _ i h),
    fun h => subsingleton_hom_shift_of_iso ((P.triangle hφ').app E).symm i
      (subsingleton_hom_shift_pull_of_iso φ.symm _ i h)⟩

/-- **Stacks 0DLC (1) gives the open of Stacks 0DLJ.**  Part (1) of Stacks 0DLC, in the shape
`AlgebraicGeometry.Space.ExistsNegativeExtLocus`, applied to the projection `X_T ⟶ T` (proper,
flat and of finite presentation by base change) with `K = E`, gives
`AlgebraicGeometry.Space.ComplexesSituation.FibreExtLocusIsOpen`: the open subspace of `T` it
provides is an open of the scheme `T`, and the fibre over a point is computed by either model. -/
theorem fibreExtLocusIsOpen_of_existsNegativeExtLocus (h : ExistsNegativeExtLocus B S hS) :
    D.FibreExtLocusIsOpen := by
  intro T E _ hE
  have hpr : IsProper B S hS (D.projection T).hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.proper
  have hfp : IsFinitePresentation B S hS (D.projection T).hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.finitePresentation
  obtain ⟨W, hW⟩ := h (D.projection T) hpr (D.projection_isFlat T) hfp E E hE.1 hE
  obtain ⟨U, hU⟩ := exists_opens_mem_iff W
  refine ⟨U, fun T₀ hT₀ y => ?_⟩
  let T₀' : SchemesOver ((schemeSpaceFunctor B S hS).obj T.left) :=
    CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map y.left)
  have h₁ := hW T₀' hT₀
  have ht : testPoint T₀' = y.left := yonedaEquiv_yoneda_map y.left
  rw [ht] at h₁
  exact (hU T₀.left y.left).symm.trans (h₁.trans (forall_congr' fun i => imp_congr_right fun _ =>
    subsingleton_baseChangeProjection_iff (D.projection T) E (isPullback_baseChangeMap D.f y) i))

end Bridge

section Descent

attribute [local instance] complexesCategory

variable {D} {I : Type u} [Category.{u} I] [IsCofiltered I] {Dg : I ⥤ BigAffineFppf B S hS}
  {c : Cone Dg}

/-- **Descent of objects.** -/
theorem descentObj (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    (h0DKW : D.RelativelyPerfectColimit) (h0DLC : D.FibreExtLocusIsOpen)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Deformation.Artin.DescentObj (complexesFunctor D) (Dg ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  rintro ⟨⟨⟨Tl, Tr, Th⟩, E, hperf, hext⟩, hA⟩
  change Tl = _ at hA
  subst hA
  obtain ⟨i, g, hg⟩ := exists_stage_factor hY hc _ rfl Th
  let A : ComplexesObject D := ⟨⟨_, Tr, Th⟩, E, hperf, hext⟩
  let F := D.stageDiagram Dg i g
  let d := D.stageCone Dg c i g A.T rfl hg
  have hd := D.isLimitStageCone Dg hc i g A.T rfl hg
  obtain ⟨hobj, -, -⟩ := h0DKW (Over i) F d hd (fun j => (Dg.obj j.left).2) c.pt.2
  obtain ⟨k, Ek, hEk, ⟨e⟩⟩ := hobj E hperf
  obtain ⟨W, hW⟩ := h0DLC (F.obj k) Ek (Dg.obj k.left).2 hEk
  have hTW : ((BigAffineFppf.toScheme B S hS).mapCone c).π.app k.left ⁻¹ᵁ W = ⊤ := by
    refine top_unique (fun t _ => ?_)
    obtain ⟨T₀, y, hT₀, ⟨t₀, rfl⟩⟩ := D.exists_fieldPoint A.T t
    have hsub := (hW T₀ hT₀ (y ≫ d.π.app k)).2 (fun n hn =>
      (D.subsingleton_fibreExt_comp_iff y (d.π.app k) Ek n).1
        ((D.subsingleton_fibreExt_iso_iff y e.symm n).1 (hext T₀ hT₀ y n hn)))
    have e₁ : (BigFppfOver.toScheme B S hS).map (y ≫ d.π.app k).left =
        (BigFppfOver.toScheme B S hS).map y.left ≫
          ((BigAffineFppf.toScheme B S hS).mapCone c).π.app k.left := by
      show (BigFppfOver.toScheme B S hS).map (y.left ≫ eqToHom rfl ≫ _) = _
      simp only [eqToHom_refl, Functor.map_comp]
      rfl
    show ((BigFppfOver.toScheme B S hS).map y.left ≫
      ((BigAffineFppf.toScheme B S hS).mapCone c).π.app k.left) t₀ ∈ W
    rw [← e₁]
    exact hsub ⟨t₀, rfl⟩
  have : ∀ j, IsAffine ((Dg ⋙ BigAffineFppf.toScheme B S hS).obj j) := fun j => (Dg.obj j).2
  have : ∀ j, CompactSpace ((Dg ⋙ BigAffineFppf.toScheme B S hS).obj j) := fun j =>
    (inferInstance : CompactSpace ((BigAffineFppf.toScheme B S hS).obj (Dg.obj j)))
  have : ∀ {j j' : I} (f : j ⟶ j'),
      _root_.AlgebraicGeometry.IsAffineHom ((Dg ⋙ BigAffineFppf.toScheme B S hS).map f) :=
    fun f => isAffineHom_of_isAffine _
  obtain ⟨j, s, hj⟩ := exists_map_eq_top (Dg ⋙ BigAffineFppf.toScheme B S hS) _ hc W hTW
  let j' : Over i := Over.mk (s ≫ k.hom)
  let s' : j' ⟶ k := Over.homMk s rfl
  let xj : ComplexesObject D :=
    { T := F.obj j'
      E := ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s'))).obj Ek
      relativelyPerfect := D.relativelyPerfectBaseChange (F.map s') Ek hEk
      noNegativeFibreExt := fun T₀ hT₀ y n hn =>
        (D.subsingleton_fibreExt_comp_iff y (F.map s') Ek n).2
          ((hW T₀ hT₀ (y ≫ F.map s')).1 (by
            rintro _ ⟨t, rfl⟩
            exact hj.ge (Set.mem_univ ((BigFppfOver.toScheme B S hS).map y.left t))) n hn) }
  let δ : ComplexesHom A xj :=
    ⟨d.π.app j', (D.coneStageComparison d s' Ek ≪≫ e).hom, Iso.isIso_hom _⟩
  refine ⟨j, ⟨xj, rfl⟩, (δ : A ⟶ xj), IsHomLift.of_fac' _ _ _ rfl rfl ?_⟩
  show eqToHom rfl ≫ _ = eqToHom rfl ≫ _ ≫ eqToHom rfl
  simp only [eqToHom_refl]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

omit [IsCofiltered I] in
/-- Two comparisons with the same base map whose composites with a morphism agree have the same
derived pullback along its base map, the comparisons of morphisms being invertible. -/
theorem pull_map_eq_of_comp_eq {A A' A'' : ComplexesObject D} (m : ComplexesHom A A')
    {b : A'.T ⟶ A''.T}
    (f f' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj A''.E ⟶ A'.E)
    (hf : IsIso f) (hf' : IsIso f')
    (h : m.comp ⟨b, f, hf⟩ = m.comp ⟨b, f', hf'⟩) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map f =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map f' := by
  have h₀ : (⟨m.base ≫ b, Functor.fibreComp (D.compComparison m.base b) m.fibre f,
      (m.comp ⟨b, f, hf⟩).isIso_fibre⟩ : ComplexesHom A A'') =
      ⟨m.base ≫ b, Functor.fibreComp (D.compComparison m.base b) m.fibre f',
        (m.comp ⟨b, f', hf'⟩).isIso_fibre⟩ := h
  have := m.isIso_fibre
  exact Functor.map_eq_of_fibreComp_eq _ m.fibre
    (eq_of_heq (ComplexesHom.mk.inj h₀).2)

omit [IsCofiltered I] in
/-- Two comparisons with the same base map whose derived pullbacks along the base map of a
morphism agree give the same composite with it. -/
theorem comp_eq_of_pull_map_eq {A A' A'' : ComplexesObject D} (m : ComplexesHom A A')
    {b : A'.T ⟶ A''.T}
    (f f' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj A''.E ⟶ A'.E)
    (hf : IsIso f) (hf' : IsIso f')
    (h : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map f =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map f') :
    m.comp ⟨b, f, hf⟩ = m.comp ⟨b, f', hf'⟩ := by
  refine complexesHom_eq_of_heq (rfl : m.base ≫ b = m.base ≫ b) (heq_of_eq ?_)
  show Functor.fibreComp (D.compComparison m.base b) m.fibre f =
    Functor.fibreComp (D.compComparison m.base b) m.fibre f'
  rw [Functor.fibreComp, Functor.fibreComp, h]

omit [IsCofiltered I] in
/-- A composite of morphisms of `Complexes_{X/Y}` is a given morphism as soon as the base maps
compose to its base map and the comparisons compose to its comparison. -/
theorem comp_eq_of_fibre {X A A' : ComplexesObject D} (m : ComplexesHom X A) (b : A.T ⟶ A'.T)
    (c : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj A'.E ⟶ A.E)
    (hc : IsIso c) (n : ComplexesHom X A') (hb : m.base ≫ b = n.base)
    (hf : Functor.fibreComp (D.tri hb) m.fibre c = n.fibre) :
    m.comp ⟨b, c, hc⟩ = n := by
  obtain ⟨nb, nf, ni⟩ := n
  change m.base ≫ b = nb at hb
  subst hb
  refine complexesHom_eq_of_heq (rfl : m.base ≫ b = m.base ≫ b) (heq_of_eq ?_)
  show Functor.fibreComp (D.compComparison m.base b) m.fibre c = nf
  rw [tri_rfl] at hf
  exact hf

omit [IsCofiltered I] in
/-- The base map of a morphism of `Complexes_{X/Y}` lying over a morphism of schemes is that
morphism. -/
theorem base_left_of_isHomLift {A A' : ComplexesObject D} (m : A ⟶ A')
    {f : A.T.left ⟶ A'.T.left} (h : (complexesFunctor D).IsHomLift f m) :
    (m : ComplexesHom A A').base.left = f :=
  (@IsHomLift.eq_of_isHomLift _ _ _ _ (complexesFunctor D) A A' f m h).symm

/-- The structure map of the source of a morphism of `Complexes_{X/Y}` is the composite of the
base map of the morphism with that of the target. -/
private theorem hom_eq_map_comp_of_base_left {A A' : ComplexesObject D} (m : ComplexesHom A A')
    {f : A.T.left ⟶ A'.T.left} (h : m.base.left = f) :
    A.T.hom = (schemeSpaceFunctor B S hS).map f ≫ A'.T.hom := by
  rw [← h]
  exact (CostructuredArrow.w m.base).symm

/-- **Descent of equalities of vertical morphisms.** -/
theorem descentEq (h0DKW : D.RelativelyPerfectColimit)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Deformation.Artin.DescentEq (complexesFunctor D) (Dg ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  rintro i ⟨⟨⟨xil, xir, gx⟩, xiE, xiP, xiN⟩, hxi⟩ ⟨⟨⟨yil, yir, gy⟩, yiE, yiP, yiN⟩, hyi⟩
    ⟨⟨⟨xl, xr, xh⟩, xE, xP, xN⟩, hx⟩ δ hδ ψ ψ' hψ hψ' hδψ
  change xil = _ at hxi
  change yil = _ at hyi
  change xl = _ at hx
  subst hxi hyi hx
  have hδb : (δ : ComplexesHom _ _).base.left =
      (BigAffineFppf.inclusion B S hS).map (c.π.app i) := base_left_of_isHomLift δ hδ
  have hψb := base_left_of_isHomLift ψ hψ
  have hψ'b := base_left_of_isHomLift ψ' hψ'
  obtain ⟨b, f, hf⟩ := ψ
  obtain ⟨b', f', hf'⟩ := ψ'
  have hbb : b = b' := CostructuredArrow.hom_ext _ _ (hψb.trans hψ'b.symm)
  subst hbb
  have hg : xh = (schemeSpaceFunctor B S hS).map
      (eqToHom rfl ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ gx := by
    rw [eqToHom_refl, Category.id_comp]
    exact hom_eq_map_comp_of_base_left _ hδb
  let F := D.stageDiagram Dg i gx
  let d := D.stageCone Dg c i gx ⟨_, xr, xh⟩ rfl hg
  have hd := D.isLimitStageCone Dg hc i gx ⟨_, xr, xh⟩ rfl hg
  let o : Over i := Over.mk (𝟙 i)
  let mx : F.obj o ⟶ ⟨_, xir, gx⟩ := CostructuredArrow.homMk (𝟙 _) (by
    show (schemeSpaceFunctor B S hS).map (𝟙 _) ≫ gx = (schemeSpaceFunctor B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (Dg.map (𝟙 i))) ≫ gx
    simp only [CategoryTheory.Functor.map_id]
    rfl)
  have hδm : d.π.app o ≫ mx = (δ : ComplexesHom _ _).base := by
    refine CostructuredArrow.hom_ext _ _ ?_
    rw [Comma.comp_left, hδb]
    show (eqToHom rfl ≫ _) ≫ 𝟙 _ = _
    rw [eqToHom_refl]
    exact (Category.comp_id _).trans (Category.id_comp _)
  obtain ⟨-, -, heq⟩ := h0DKW (Over i) F d hd (fun j => (Dg.obj j.left).2) c.pt.2
  have hfib := pull_map_eq_of_comp_eq (δ : ComplexesHom _ _) f f' hf hf' hδψ
  have hfib' := D.pull_map_eq_of_tri' hδm hfib
  obtain ⟨k, t, hkt⟩ := heq o
    (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap mx)).obj
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj yiE))
    (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap mx)).obj xiE)
    (D.relativelyPerfectBaseChange mx _ (D.relativelyPerfectBaseChange b _ yiP))
    (D.relativelyPerfectBaseChange mx _ xiP) _ _ hfib'
  let hx' := F.map t ≫ mx
  let xk := pullbackObject (⟨⟨_, xir, gx⟩, xiE, xiP, xiN⟩ : ComplexesObject D) hx'
    (D.relativelyPerfectBaseChange hx' xiE xiP)
  let dx := pullbackHom (⟨⟨_, xir, gx⟩, xiE, xiP, xiN⟩ : ComplexesObject D) hx'
    (D.relativelyPerfectBaseChange hx' xiE xiP)
  refine ⟨k.left, t.left, ⟨xk, rfl⟩, (dx : xk ⟶ _), IsHomLift.of_fac' _ _ _ rfl rfl ?_, ?_⟩
  · show (BigAffineFppf.inclusion B S hS).map (Dg.map t.left) ≫ 𝟙 _ =
        𝟙 _ ≫ (BigAffineFppf.inclusion B S hS).map (Dg.map t.left) ≫ 𝟙 _
    exact (Category.comp_id _).trans ((Category.id_comp _).trans (Category.comp_id _)).symm
  · exact comp_eq_of_pull_map_eq dx f f' hf hf' (D.pull_map_eq_of_tri'' rfl hkt)

/-- **Descent of vertical morphisms.** -/
theorem descentHom (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    (h0DKW : D.RelativelyPerfectColimit)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Deformation.Artin.DescentHom (complexesFunctor D) (Dg ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  rintro i ⟨⟨⟨xil, xir, gx⟩, xiE, xiP, xiN⟩, hxi⟩ ⟨⟨⟨yil, yir, gy⟩, yiE, yiP, yiN⟩, hyi⟩
    ⟨⟨⟨xl, xr, xh⟩, xE, xP, xN⟩, hx⟩ ⟨⟨⟨yl, yr, yh⟩, yE, yP, yN⟩, hy⟩ δ ε hδ hε φ hφ
  change xil = _ at hxi
  change yil = _ at hyi
  change xl = _ at hx
  change yl = _ at hy
  subst hxi hyi hx hy
  have hδb : (δ : ComplexesHom _ _).base.left = (BigAffineFppf.inclusion B S hS).map (c.π.app i) :=
    base_left_of_isHomLift δ hδ
  have hεb : (ε : ComplexesHom _ _).base.left = (BigAffineFppf.inclusion B S hS).map (c.π.app i) :=
    base_left_of_isHomLift ε hε
  have hφb : (φ : ComplexesHom _ _).base.left = 𝟙 _ := base_left_of_isHomLift φ hφ
  have hgx : xh = (schemeSpaceFunctor B S hS).map (eqToHom rfl ≫
      (BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ gx := by
    rw [eqToHom_refl, Category.id_comp]
    exact hom_eq_map_comp_of_base_left _ hδb
  have hgy : yh = (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map
      (c.π.app i)) ≫ gy := hom_eq_map_comp_of_base_left _ hεb
  have hxy : yh = xh := by simpa using (hom_eq_map_comp_of_base_left _ hφb).symm
  have heqg : (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map
      (c.π.app i)) ≫ gx =
      (schemeSpaceFunctor B S hS).map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ≫ gy := by
    rw [← hgy, hxy, hgx, eqToHom_refl, Category.id_comp]
  obtain ⟨k₀, s₀, hs₀⟩ := exists_stage_eq hY hc i gx gy heqg
  let F := D.stageDiagram Dg i gx
  let d := D.stageCone Dg c i gx ⟨_, xr, xh⟩ rfl hgx
  have hd := D.isLimitStageCone Dg hc i gx ⟨_, xr, xh⟩ rfl hgx
  obtain ⟨-, hhom, heq⟩ := h0DKW (Over i) F d hd (fun j => (Dg.obj j.left).2) c.pt.2
  let o : Over i := Over.mk s₀
  let mx : F.obj o ⟶ ⟨_, xir, gx⟩ := CostructuredArrow.homMk
      ((BigAffineFppf.inclusion B S hS).map (Dg.map s₀)) rfl
  let my : F.obj o ⟶ ⟨_, yir, gy⟩ := CostructuredArrow.homMk
      ((BigAffineFppf.inclusion B S hS).map (Dg.map s₀)) hs₀.symm
  have hπ : (eqToHom rfl ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app k₀)) ≫
      (BigAffineFppf.inclusion B S hS).map (Dg.map s₀) =
      (BigAffineFppf.inclusion B S hS).map (c.π.app i) := by
    rw [eqToHom_refl, Category.id_comp, ← Functor.map_comp, c.w s₀]
  have hδm : d.π.app o ≫ mx = (δ : ComplexesHom _ _).base :=
    CostructuredArrow.hom_ext _ _ (by rw [Comma.comp_left, hδb]; exact hπ)
  let φε := (φ : ComplexesHom _ _).comp (ε : ComplexesHom _ _)
  have hφε : φε.base = (φ : ComplexesHom _ _).base ≫ (ε : ComplexesHom _ _).base := rfl
  have hεm : d.π.app o ≫ my = φε.base :=
    CostructuredArrow.hom_ext _ _ (by
      rw [hφε, Comma.comp_left, Comma.comp_left, hφb, hεb, Category.id_comp]; exact hπ)
  let eδ := @asIso _ _ _ _ (δ : ComplexesHom _ _).fibre (δ : ComplexesHom _ _).isIso_fibre
  let eφε := @asIso _ _ _ _ φε.fibre φε.isIso_fibre
  let Φ := (D.triApp hεm yiE).symm ≪≫ eφε ≪≫ eδ.symm ≪≫ D.triApp hδm xiE
  obtain ⟨k, t, ψ, hψ⟩ := D.exists_stage_iso d hhom heq
    (D.relativelyPerfectBaseChange my yiE yiP) (D.relativelyPerfectBaseChange mx xiE xiP) Φ
  let xk : ComplexesObject D :=
    ⟨F.obj k, ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap mx)).obj xiE),
      D.relativelyPerfectBaseChange _ _ (D.relativelyPerfectBaseChange mx xiE xiP),
      D.hasNoNegativeFibreExt_pull _ _ (D.hasNoNegativeFibreExt_pull mx xiE xiN)⟩
  let yk : ComplexesObject D :=
    ⟨F.obj k, ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map t))).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap my)).obj yiE),
      D.relativelyPerfectBaseChange _ _ (D.relativelyPerfectBaseChange my yiE yiP),
      D.hasNoNegativeFibreExt_pull _ _ (D.hasNoNegativeFibreExt_pull my yiE yiN)⟩
  let dx : ComplexesHom xk ⟨⟨_, xir, gx⟩, xiE, xiP, xiN⟩ :=
    ⟨F.map t ≫ mx, (D.triApp (rfl : F.map t ≫ mx = F.map t ≫ mx) xiE).hom, Iso.isIso_hom _⟩
  let dy : ComplexesHom yk ⟨⟨_, yir, gy⟩, yiE, yiP, yiN⟩ :=
    ⟨F.map t ≫ my, (D.triApp (rfl : F.map t ≫ my = F.map t ≫ my) yiE).hom, Iso.isIso_hom _⟩
  have hq' : F.map t ≫ my = 𝟙 (F.obj k) ≫ F.map t ≫ my := (Category.id_comp _).symm
  let c' := (D.triApp hq' yiE ≪≫ ψ).hom
  obtain ⟨ψc, hψcb, hψc⟩ : ∃ ψc : ComplexesHom xk yk, ψc.base = 𝟙 (F.obj k) ∧
      ψc.comp dy = ⟨𝟙 (F.obj k) ≫ F.map t ≫ my, c', Iso.isIso_hom _⟩ :=
    ⟨@fillIn B S hS D _ yk xk dy (𝟙 (F.obj k)) c' (Iso.isIso_hom _), rfl,
      @fillIn_comp B S hS D _ yk xk dy (𝟙 (F.obj k)) c' (Iso.isIso_hom _)⟩
  let δk : ComplexesHom ⟨⟨_, xr, xh⟩, xE, xP, xN⟩ xk :=
    ⟨d.π.app k, (D.triApp (d.w t) (((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap mx)).obj xiE)).inv ≫ (D.triApp hδm xiE).inv ≫
      (δ : ComplexesHom _ _).fibre,
      IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' (Iso.isIso_inv _)
        (δ : ComplexesHom _ _).isIso_fibre)⟩
  have hw : t.left ≫ s₀ = k.hom := Over.w t
  have hb₁ : d.π.app k ≫ F.map t ≫ mx = (δ : ComplexesHom _ _).base := by
    rw [← Category.assoc, d.w t, hδm]
  have hb₂ : d.π.app k ≫ 𝟙 (F.obj k) ≫ F.map t ≫ my = φε.base := by
    rw [Category.id_comp, ← Category.assoc, d.w t, hεm]
  have hfac : (BigAffineFppf.inclusion B S hS).map (Dg.map t.left) ≫
      (BigAffineFppf.inclusion B S hS).map (Dg.map s₀) = 𝟙 _ ≫
        (BigAffineFppf.inclusion B S hS).map (Dg.map k.hom) ≫ 𝟙 _ := by
    rw [← Functor.map_comp, ← Dg.map_comp, hw]
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  refine ⟨k.left, k.hom, ⟨xk, rfl⟩, ⟨yk, rfl⟩, (dx : xk ⟶ _), (dy : yk ⟶ _), (δk : _ ⟶ xk),
    (ψc : xk ⟶ yk), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsHomLift.of_fac' _ _ _ rfl rfl hfac
  · exact IsHomLift.of_fac' _ _ _ rfl rfl hfac
  · refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    show eqToHom rfl ≫ _ = eqToHom rfl ≫ _ ≫ eqToHom rfl
    simp only [eqToHom_refl]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    show ψc.base.left = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    rw [hψcb]
    exact ((Category.id_comp _).trans (Category.id_comp _)).symm
  · exact D.comp_eq_of_fibre δk _ _ _ _ hb₁ (D.fibre_identity₁' (d.w t) rfl hb₁ hδm xiE _)
  · show δk.comp (ψc.comp dy) = φε
    rw [hψc]
    refine D.comp_eq_of_fibre δk _ _ _ _ hb₂ (D.fibre_identity₂' (d.w t) hδm hεm hq' hb₂
      (δ : ComplexesHom _ _).fibre eδ.inv eδ.inv_hom_id φε.fibre ψ.hom ?_)
    exact hψ.symm.trans (Iso.trans₄_symm_hom _ _ _ _)

end Descent

section Main

attribute [local instance] complexesCategory

variable {D}

/-- **Stacks 0DLJ, reduced to Stacks 0DKW and Stacks 0DLC (1).** -/
theorem isLimitPreserving_of_fibreExtLocusIsOpen
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    (h0DKW : D.RelativelyPerfectColimit) (h0DLC : D.FibreExtLocusIsOpen) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D)
        (complexesFunctor_isFiberedInGroupoids D)) := by
  intro I _ _ Dg c hc
  have hp := complexesFunctor_isFiberedInGroupoids D
  have : (complexesFunctor D).IsFibered := hp.isFibered
  have := Deformation.Artin.faithful_of_descentEq (complexesFunctor D) hp _ _
    (descentEq h0DKW hc)
  have := Deformation.Artin.full_of_descentHom (complexesFunctor D) hp _ _
    (descentHom hY h0DKW hc)
  have := Deformation.Artin.essSurj_of_descentObj (complexesFunctor D) hp _ _
    (descentObj hY h0DKW h0DLC hc)
  exact { }

/-- **Stacks 0DLJ, reduced to Stacks 0DKW and Stacks 0DLC (1).**  In Situation 0DLE, if `Y` is
locally of finite presentation over `S`, the projection `p : Complexes_{X/Y} ⥤ (Sch/S)_fppf` is
limit preserving (Stacks 07XL), given Stacks 0DKW (`h0DKW`, not yet proved here) and
part (1) of Stacks 0DLC in the shape `AlgebraicGeometry.Space.ExistsNegativeExtLocus` (`h0DLC`,
pending on Stacks 0DKY, not yet proved here).  This is the hypothesis `h0DLJ` of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`. -/
theorem isLimitPreserving_of_existsNegativeExtLocus
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    (h0DKW : D.RelativelyPerfectColimit) (h0DLC : ExistsNegativeExtLocus B S hS) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D)
        (complexesFunctor_isFiberedInGroupoids D)) :=
  isLimitPreserving_of_fibreExtLocusIsOpen hY h0DKW
    (D.fibreExtLocusIsOpen_of_existsNegativeExtLocus h0DLC)

end Main

end AlgebraicGeometry.Space.ComplexesSituation

end
