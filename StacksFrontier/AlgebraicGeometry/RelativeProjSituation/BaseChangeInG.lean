module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.DegreewiseBaseChange

/-!
# The base change of graded section rings is functorial in the morphism of base schemes

`Stacks.RelativeProj.Situation.gradedBaseChange g Φ W W' h` depends on a morphism
`g : S' ⟶ S` of base schemes together with an identification `Φ` of the graded algebra of `s'`
with the pullback along `g` of the graded algebra of `s`. Functoriality in the pair of opens
`(W, W')` is already available; this file supplies the two remaining laws, in `g` itself.

* **Identity.** For `g = 𝟙 S` and `Φ` the canonical identification `(𝟙 S)^*𝒜 ≅ 𝒜`, the base
  change `𝒜(W) ⟶ 𝒜(W')` is the restriction map of the section rings.
* **Composition.** For `q : S'' ⟶ S'` and `g : S' ⟶ S` with identifications `Φ` for `g` and
  `Ψ` for `q`, base-changing along `g` and then along `q` is base-changing along `q ≫ g`, for
  the identification whose degreewise component is `Ψ_n ∘ q^*Φ_n` read through the canonical
  comparison `(q ≫ g)^*𝒜_n ≅ q^*(g^*𝒜_n)`.

## Main definitions

* `Stacks.Conormal.gradedPullbackId`: the canonical identification of `(𝟙 X)^*A` with `A`, as a
  unital homomorphism of sheaves of graded algebras.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.pullbackIdHom_pullbackSection`: the identity
  comparison carries a section pulled back along `𝟙 X` to the restricted section.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullbackSection_id`: every section of
  `(𝟙 X)^*M` over an open is the pullback of a section of `M` over that same open.
* `Stacks.RelativeProj.Situation.gradedBaseChange_id`: **the identity law.** Base-changing
  along `𝟙 S` is restricting.
* `Stacks.RelativeProj.Situation.pieceSectionHom_comp`: the degreewise components compose, for
  the canonical comparison in degree `n`.
* `Stacks.RelativeProj.Situation.gradedBaseChange_comp`: **the composition law.** Given the
  degreewise compatibility, base-changing twice is base-changing along the composite.

## Implementation notes

The identity comparison is `AlgebraicGeometry.Scheme.Modules.pullbackId`, and the content of
`Stacks.Conormal.gradedPullbackId` is that it is multiplicative and unital. Multiplicativity is
an equation at *arbitrary* local sections of `(𝟙 X)^*A_i`, whereas
`Stacks.Conormal.gradedPullback_mul_pullbackSection` describes the multiplication only on
pulled-back sections. For the identity morphism the two coincide:
`Stacks.AlgebraicGeometry.ModuleLimits.exists_pullbackSection_id` says that over an open `U`
every section of `(𝟙 X)^*M` is the pullback of a section of `M` over `U`, because
`pullbackId` is an isomorphism and its inverse exhibits the preimage. That is what makes the
identity law unconditional, and it is exactly what fails for a general composite: over an open
of `S''` a section of `(q ≫ g)^*A_i` is not a pulled-back section, so multiplicativity of the
canonical comparison `(q ≫ g)^*A_i ≅ q^*(g^*A_i)` is not reducible to the section formula and
would need the monoidal pseudofunctoriality of pullback. The composition law is therefore
stated for an identification `Θ` whose degreewise components are given by the canonical
comparison, rather than for an identification constructed here.

Both graded-ring statements are proved by `DirectSum.induction_on` from the degreewise ones,
through `Stacks.RelativeProj.Situation.sectionRingBaseChange_of` and the `restrict_of` field of
the section-ring structure, and are then upgraded to `GradedRingHom` equalities by
extensionality, which is the form `AlgebraicGeometry.Proj.map_comp` consumes.

No `@[stacks]` attribute is attached: these are functoriality statements about a construction of
this development, not the content of a tag.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum
open HomogeneousIdeal

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### The identity comparison on sections -/

/-- Restricting a section along the identity inclusion of an open does nothing. -/
private theorem val_map_self {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (h : U ≤ U)
    (x : M.val.obj (op U)) : M.val.map (homOfLE h).op x = x := by
  rw [show (homOfLE h).op = 𝟙 (op U) from Subsingleton.elim _ _,
    ← PresheafOfModules.presheaf_map_apply_coe, M.val.presheaf.map_id]
  rfl

/-- **The identity comparison undoes the unit of `(𝟙 X)^* ⊣ (𝟙 X)_*`.** This is
`CategoryTheory.unit_conjugateEquiv` for the identity adjunction, read on sections. -/
public theorem pullbackIdHom_unit {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (a : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackId X).hom.app M).val.app (op U)
        (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M).val.app (op U) a)
      = a := by
  have h := CategoryTheory.unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact (congrArg (fun t => t.val.app (op U) a) h).symm

/-- **The identity comparison carries a pulled-back section to the restricted section.** -/
public theorem pullbackIdHom_pullbackSection {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
    (h : V ≤ (𝟙 X) ⁻¹ᵁ U) (h' : V ≤ U) (a : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackId X).hom.app M).val.app (op V)
        (Scheme.Modules.pullbackSection (𝟙 X) M U V h a)
      = M.val.map (homOfLE h').op a :=
  (PresheafOfModules.naturality_apply ((Scheme.Modules.pullbackId X).hom.app M).val
      (homOfLE h).op _).trans
    (congrArg (fun z => M.val.map (homOfLE h').op z) (pullbackIdHom_unit M U a))

/-- The identity comparison carries the pullback of a section to the open it already lives on
back to that section. -/
public theorem pullbackIdHom_pullbackSection_self {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (a : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackId X).hom.app M).val.app (op U)
        (Scheme.Modules.pullbackSection (𝟙 X) M U U le_rfl a) = a :=
  (pullbackIdHom_pullbackSection M U U le_rfl le_rfl a).trans (val_map_self M U le_rfl a)

/-- The inverse of the identity comparison is the pullback of a section to the open it already
lives on. -/
public theorem pullbackId_inv_app {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (a : M.val.obj (op U)) :
    (inv ((Scheme.Modules.pullbackId X).hom.app M)).val.app (op U) a
      = Scheme.Modules.pullbackSection (𝟙 X) M U U le_rfl a :=
  (congrArg (fun z => (inv ((Scheme.Modules.pullbackId X).hom.app M)).val.app (op U) z)
      (pullbackIdHom_pullbackSection_self M U a)).symm.trans
    (inv_val_app_apply ((Scheme.Modules.pullbackId X).hom.app M) U _)

/-- **Every section of `(𝟙 X)^*M` over an open is a pulled-back section**, namely the pullback
of its image under the identity comparison. -/
public theorem exists_pullbackSection_id {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (x : ((Scheme.Modules.pullback (𝟙 X)).obj M).val.obj (op U)) :
    ∃ a : M.val.obj (op U), Scheme.Modules.pullbackSection (𝟙 X) M U U le_rfl a = x := by
  exact ⟨_, (pullbackId_inv_app M U _).symm.trans
    (inv_val_app_apply ((Scheme.Modules.pullbackId X).hom.app M) U x)⟩

end Stacks.AlgebraicGeometry.ModuleLimits

namespace Stacks.Conormal

open Stacks.AlgebraicGeometry.ModuleLimits

/-- **The canonical identification of `(𝟙 X)^*A` with `A`**, as a unital homomorphism of
sheaves of graded algebras. In each degree it is
`AlgebraicGeometry.Scheme.Modules.pullbackId`; multiplicativity and unitality hold because over
an open every section of `(𝟙 X)^*A_i` is a pulled-back section, where the multiplication of the
pullback is described by `Stacks.Conormal.gradedPullback_mul_pullbackSection`. -/
public def gradedPullbackId {X : Scheme.{u}}
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) :
    SheafOfModules.GradedAlgebra.UnitalHom (gradedPullback (𝟙 X) A) A where
  app n := (Scheme.Modules.pullbackId X).hom.app (A.piece n)
  map_mul i j U x y := by
    obtain ⟨U⟩ := U
    obtain ⟨a, rfl⟩ := exists_pullbackSection_id (A.piece i) U x
    obtain ⟨b, rfl⟩ := exists_pullbackSection_id (A.piece j) U y
    refine Eq.trans ((congrArg (fun z =>
        ((Scheme.Modules.pullbackId X).hom.app (A.piece (i + j))).val.app (op U) z)
          (gradedPullback_mul_pullbackSection (𝟙 X) A i j U a b)).trans
      (pullbackIdHom_pullbackSection_self (A.piece (i + j)) U
        ((A.mul i j).app (op U) a b))) ?_
    exact ((congrArg (fun p => (A.mul i j).app (op U) p
          (((Scheme.Modules.pullbackId X).hom.app (A.piece j)).val.app (op U)
            (Scheme.Modules.pullbackSection (𝟙 X) (A.piece j) U U le_rfl b)))
        (pullbackIdHom_pullbackSection_self (A.piece i) U a)).trans
      (congrArg (fun q => (A.mul i j).app (op U) a q)
        (pullbackIdHom_pullbackSection_self (A.piece j) U b))).symm
  map_one U := by
    obtain ⟨U⟩ := U
    exact (congrArg (fun z =>
        ((Scheme.Modules.pullbackId X).hom.app (A.piece 0)).val.app (op U) z)
      (gradedPullback_one_eval (𝟙 X) A U)).trans
        (pullbackIdHom_pullbackSection_self (A.piece 0) U _)

/-- In degree `n`, `gradedPullbackId A` is `Scheme.Modules.pullbackId X` at the piece `A_n`. -/
@[simp] public theorem gradedPullbackId_app {X : Scheme.{u}}
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (n : ℤ) :
    (gradedPullbackId A).app n = (Scheme.Modules.pullbackId X).hom.app (A.piece n) := rfl

/-- The identity identification is an isomorphism in every degree. -/
public instance isIso_gradedPullbackId_app {X : Scheme.{u}}
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (n : ℤ) :
    IsIso ((gradedPullbackId A).app n) :=
  inferInstanceAs (IsIso ((Scheme.Modules.pullbackId X).app (A.piece n)).hom)

end Stacks.Conormal

namespace Stacks.RelativeProj.Situation

open Stacks.AlgebraicGeometry.ModuleLimits

/-! ### The identity law -/

variable {s : Situation.{u}}

/-- **The degreewise base change along the identity is restriction.** -/
public theorem pieceSectionHom_id (n : ℕ) (W W' : s.base.Opens)
    (h : W' ≤ (𝟙 s.base) ⁻¹ᵁ W) (h' : W' ≤ W) (a : s.sectionPieces W n) :
    pieceSectionHom (𝟙 s.base) (Stacks.Conormal.gradedPullbackId s.algebra) n W W' h a
      = (s.algebra.piece (n : ℤ)).val.map (homOfLE h').op a :=
  (pieceSectionHom_apply (𝟙 s.base) (Stacks.Conormal.gradedPullbackId s.algebra) n W W' h
      a).trans
    (pullbackIdHom_pullbackSection (s.algebra.piece (n : ℤ)) W W' h h' a)

/-- **The base change of section rings along the identity is restriction.** -/
public theorem sectionRingBaseChange_id (W W' : s.base.Opens)
    (h : W' ≤ (𝟙 s.base) ⁻¹ᵁ W) (h' : W' ≤ W) (x : s.sectionRing W) :
    sectionRingBaseChange (𝟙 s.base) (Stacks.Conormal.gradedPullbackId s.algebra) W W' h x
      = sectionRingRestrict s W' W h' x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n a =>
      exact (sectionRingBaseChange_of (𝟙 s.base) (Stacks.Conormal.gradedPullbackId s.algebra)
            W W' h n a).trans
        ((congrArg (DirectSum.of (s.sectionPieces W') n)
            (pieceSectionHom_id n W W' h h' a)).trans
          ((sectionRingStructure s).restrict_of W' W h' n a).symm)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **The identity law.** Base-changing the graded section rings along `𝟙 S`, with the canonical
identification of `(𝟙 S)^*𝒜` with `𝒜`, is the restriction map of `s`. -/
public theorem gradedBaseChange_id (W W' : s.base.Opens) (h : W' ≤ (𝟙 s.base) ⁻¹ᵁ W)
    (h' : W' ≤ W) :
    gradedBaseChange (𝟙 s.base) (Stacks.Conormal.gradedPullbackId s.algebra) W W' h
      = s.gradedRestrict h' :=
  DFunLike.ext _ _ fun x => sectionRingBaseChange_id W W' h h' x

/-! ### The composition law -/

section Comp

variable {s' s'' : Situation.{u}} (g : s'.base ⟶ s.base) (q : s''.base ⟶ s'.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  (Ψ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback q s'.algebra) s''.algebra)
  (Θ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback (q ≫ g) s.algebra) s''.algebra)

/-- **The degreewise components compose.** If in degree `n` the identification `Θ` for the
composite is the canonical one — the comparison `q^*(g^*𝒜ₙ) ≅ (q ≫ g)^*𝒜ₙ` of
`Stacks.AlgebraicGeometry.ModuleLimits.canHom` followed by `Θₙ` is `q^*Φₙ` followed by `Ψₙ` —
then pulling a homogeneous section back along `g` and then along `q` is pulling it back along
`q ≫ g`.

This is `Stacks.AlgebraicGeometry.ModuleLimits.canHom_val_app_pullbackSection` together with
naturality of pulling a section back in the module. -/
public theorem pieceSectionHom_comp (n : ℕ)
    (hΘ : canHom q g (q ≫ g) rfl (s.algebra.piece (n : ℤ)) ≫ Θ.app (n : ℤ) =
      (Scheme.Modules.pullback q).map (Φ.app (n : ℤ)) ≫ Ψ.app (n : ℤ))
    (W : s.base.Opens) (W' : s'.base.Opens) (W'' : s''.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (h' : W'' ≤ q ⁻¹ᵁ W') (h'' : W'' ≤ (q ≫ g) ⁻¹ᵁ W)
    (a : s.sectionPieces W n) :
    pieceSectionHom q Ψ n W' W'' h' (pieceSectionHom g Φ n W W' h a)
      = pieceSectionHom (q ≫ g) Θ n W W'' h'' a := by
  set d : ((Scheme.Modules.pullback q).obj
      ((Scheme.Modules.pullback g).obj (s.algebra.piece (n : ℤ)))).val.obj (op W'') :=
    Scheme.Modules.pullbackSection q
      ((Scheme.Modules.pullback g).obj (s.algebra.piece (n : ℤ))) W' W'' h'
      (Scheme.Modules.pullbackSection g (s.algebra.piece (n : ℤ)) W W' h a) with hd
  have hleft : pieceSectionHom q Ψ n W' W'' h' (pieceSectionHom g Φ n W W' h a)
      = ((Scheme.Modules.pullback q).map (Φ.app (n : ℤ)) ≫ Ψ.app (n : ℤ)).val.app (op W'') d :=
    (pieceSectionHom_apply q Ψ n W' W'' h' _).trans
      (congrArg (fun z => (Ψ.app (n : ℤ)).val.app (op W'') z)
        (Scheme.Modules.pullbackSection_naturality q (Φ.app (n : ℤ)) W' W'' h'
          (Scheme.Modules.pullbackSection g (s.algebra.piece (n : ℤ)) W W' h a)).symm)
  have hright : pieceSectionHom (q ≫ g) Θ n W W'' h'' a
      = (canHom q g (q ≫ g) rfl (s.algebra.piece (n : ℤ)) ≫ Θ.app (n : ℤ)).val.app (op W'') d :=
    (pieceSectionHom_apply (q ≫ g) Θ n W W'' h'' a).trans
      (congrArg (fun z => (Θ.app (n : ℤ)).val.app (op W'') z)
        (canHom_val_app_pullbackSection q g (q ≫ g) rfl (s.algebra.piece (n : ℤ)) W W' W''
          h h' h'' a).symm)
  exact hleft.trans ((congrArg (fun k : (Stacks.Conormal.gradedPullback q
      (Stacks.Conormal.gradedPullback g s.algebra)).piece (n : ℤ) ⟶
        s''.algebra.piece (n : ℤ) => k.val.app (op W'') d) hΘ).symm.trans hright.symm)

/-- **The composition law on the section rings.** Given the degreewise compatibility,
base-changing along `g` and then along `q` is base-changing along `q ≫ g`. -/
public theorem sectionRingBaseChange_comp (W : s.base.Opens) (W' : s'.base.Opens)
    (W'' : s''.base.Opens) (h : W' ≤ g ⁻¹ᵁ W) (h' : W'' ≤ q ⁻¹ᵁ W')
    (h'' : W'' ≤ (q ≫ g) ⁻¹ᵁ W)
    (hΘ : ∀ (n : ℕ) (a : s.sectionPieces W n),
      pieceSectionHom q Ψ n W' W'' h' (pieceSectionHom g Φ n W W' h a)
        = pieceSectionHom (q ≫ g) Θ n W W'' h'' a)
    (x : s.sectionRing W) :
    sectionRingBaseChange q Ψ W' W'' h' (sectionRingBaseChange g Φ W W' h x)
      = sectionRingBaseChange (q ≫ g) Θ W W'' h'' x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of n a =>
      exact (congrArg (fun z : s'.sectionRing W' => sectionRingBaseChange q Ψ W' W'' h' z)
          (sectionRingBaseChange_of g Φ W W' h n a)).trans
        ((sectionRingBaseChange_of q Ψ W' W'' h' n _).trans
          ((congrArg (DirectSum.of (s''.sectionPieces W'') n) (hΘ n a)).trans
            (sectionRingBaseChange_of (q ≫ g) Θ W W'' h'' n a).symm))
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- **The composition law.** Given the degreewise compatibility, the composite of the two base
changes of graded section rings is the base change along `q ≫ g`. This is the form
`AlgebraicGeometry.Proj.map_comp` consumes. -/
public theorem gradedBaseChange_comp (W : s.base.Opens) (W' : s'.base.Opens)
    (W'' : s''.base.Opens) (h : W' ≤ g ⁻¹ᵁ W) (h' : W'' ≤ q ⁻¹ᵁ W')
    (h'' : W'' ≤ (q ≫ g) ⁻¹ᵁ W)
    (hΘ : ∀ (n : ℕ) (a : s.sectionPieces W n),
      pieceSectionHom q Ψ n W' W'' h' (pieceSectionHom g Φ n W W' h a)
        = pieceSectionHom (q ≫ g) Θ n W W'' h'' a) :
    (gradedBaseChange q Ψ W' W'' h').comp (gradedBaseChange g Φ W W' h)
      = gradedBaseChange (q ≫ g) Θ W W'' h'' :=
  DFunLike.ext _ _ fun x =>
    sectionRingBaseChange_comp g q Φ Ψ Θ W W' W'' h h' h'' hΘ x

end Comp

/-! ### The identity law for the comparison morphism of relative `Proj` -/

/-- **On a chart, the comparison morphism along the identity is the chart transition.** The base
change along `𝟙 S` is the restriction map by
`Stacks.RelativeProj.Situation.gradedBaseChange_id`, and `Proj.map` of the restriction map is
the comparison morphism of charts of `s`. -/
public theorem chartBaseChangeHom_id (W W' : s.base.affineOpens)
    (h : W'.1 ≤ (𝟙 s.base) ⁻¹ᵁ W.1) :
    chartBaseChangeHom (𝟙 s.base) (Stacks.Conormal.gradedPullbackId s.algebra)
        (fun m => Stacks.Conormal.isIso_gradedPullbackId_app s.algebra (m : ℤ)) W W' h
      = relativeProjChart s W' := by
  have h' : W' ≤ W := h
  have hirr : (s.chartGrading W')₊ ≤ ((s.chartGrading W)₊).map (s.gradedRestrict h') :=
    s.chartsCartesian.irrelevant_le h'
  rw [chartBaseChangeHom, Proj.map_congr (gradedBaseChange_id W.1 W'.1 h h') _ hirr,
    show AlgebraicGeometry.Proj.map (s.gradedRestrict h') hirr =
      projInclusionMap s W'.1 W.1 h' W'.2 W.2 from rfl,
    relativeProjChart_transition s h']

/-- **The base-change comparison morphism along the identity is the identity.** Two morphisms
out of `relativeProj s` that agree on every chart of the base-change cover are equal, and on
each chart the comparison morphism is the chart transition of `s` by
`Stacks.RelativeProj.Situation.chartBaseChangeHom_id`. -/
public theorem relativeProjBaseChange_id :
    relativeProjBaseChange (𝟙 s.base) (Stacks.Conormal.gradedPullbackId s.algebra)
        (fun m => Stacks.Conormal.isIso_gradedPullbackId_app s.algebra (m : ℤ))
      = 𝟙 (relativeProj s) := by
  refine (baseChangeCover (𝟙 s.base)).hom_ext _ _ fun p => ?_
  refine (relativeProjChart_comp_relativeProjBaseChange (𝟙 s.base)
    (Stacks.Conormal.gradedPullbackId s.algebra)
    (fun m => Stacks.Conormal.isIso_gradedPullbackId_app s.algebra (m : ℤ)) p).trans ?_
  exact (chartBaseChangeHom_id p.1.2 p.1.1 p.2).trans (Category.comp_id _).symm

end Stacks.RelativeProj.Situation

end
