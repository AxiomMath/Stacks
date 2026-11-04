module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic

/-!
# Pullback commutes with completion

Let `g : X ⟶ Y` be a morphism of Noetherian schemes, let `𝒥 ⊆ 𝒪_Y` be a quasi-coherent sheaf of
ideals and set `ℐ = g^{-1}𝒥 𝒪_X`. For a coherent `𝒪_Y`-module `M` the termwise pullback of the
completion `M^ = (M / 𝒥 ⁿ⁺¹M)` is the completion of `g^*M` along `ℐ`:

`g^*(M^) ≅ (g^*M)^` in `Coh(X, ℐ)`.

The comparison is the canonical one: at level `n` it is the map through which the pullback of the
projection `M ⟶ M / 𝒥 ⁿ⁺¹M` becomes the projection `g^*M ⟶ g^*M / ℐ ⁿ⁺¹g^*M`, and it is natural
in `M`.

Everything comes from one input, `Stacks.Coherent.exists_functor_idealPowerQuotient_iso`: a right
exact functor compatible with ideal-power multiples carries `M / 𝒥 ⁿM` to `L M / ℐ ⁿ L M`
compatibly with the two quotient projections. Termwise pullback is such a functor — it is a left
adjoint, hence right exact, and the compatibility with ideal-power multiples is
`Stacks.Algebraization.pullback_idealPowerMultiple_comp_eq_zero_iff`. Assembling the levelwise
comparisons into a morphism of inverse systems, and proving naturality, uses nothing else: every
map out of a term of a completion is determined by its precomposition with the projection from
the module, because that projection is an epimorphism
(`Stacks.Coherent.epi_completionProjection`) and termwise pullback, being a left adjoint,
preserves epimorphisms.

## Main definitions

* `Stacks.Coherent.pullbackCompletionIso` — **the comparison isomorphism `g^*(M^) ≅ (g^*M)^`.**
* `Stacks.Coherent.pullbackCompletionComparison` — its underlying levelwise isomorphism.
* `Stacks.Coherent.pullbackIdealPowerQuotientIso` — the pullback of `M / 𝒥 ⁿM` is
  `g^*M / ℐ ⁿ g^*M`.

## Main results

* `Stacks.Coherent.pullbackCompletionIso_hom_app_projection` — the comparison is normalised by
  the projections: the pullback of the `n`-th projection of `M`, read through the comparison, is
  the `n`-th projection of `g^*M`.
* `Stacks.Coherent.pullbackCompletionIso_naturality` — **the comparison is natural in the
  module.**

## Implementation notes

The terms of a completion are indexed so that level `n` is the quotient by the `(n+1)`-st power
of the ideal, following `Stacks.Algebraization.completionFunctor`; the levelwise comparison at
`n` is therefore the one for the exponent `n + 1`.

`Stacks.Algebraization.completionFunctor` does not expose its definition, so the identification of
its `n`-th term with `Stacks.Algebraization.idealPowerQuotient` is the propositional equality
`Stacks.Algebraization.completionFunctor_obj` and not a definitional one; the levelwise comparison
therefore carries two `eqToHom`s. They cancel against the ones hidden inside
`Stacks.Algebraization.completionProjection` as soon as the comparison is composed with a
projection, which is the only way it is ever used; that cancellation is isolated as
`Stacks.Coherent.map_comp_eqToHom_comparison` in an abstract category, where the automation is
not obstructed by the two descriptions of the category of `𝒪_X`-modules.

`Stacks.Algebraization.completionProjection_transition` records the compatibility of the
projections with the successor transition maps only; the compatibility with an arbitrary
transition map, needed for naturality in the index, is obtained from it by induction.

## References

* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

open Stacks.Algebraization

/-! ### Two pieces of bookkeeping -/

/-- Cancelling the identification of two descriptions of an object out of a comparison map.

If `F f ≫ q = s` then, for any equality `p` of the target of `f` with another object, the map
`f` followed by `p` and then by the comparison `F p ≫ q ≫ r` is `s ≫ r`: the two transports
cancel. This is the shape in which the levelwise comparison of a completion with the adic
quotients is composed with a projection. -/
private lemma map_comp_eqToHom_comparison {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B B' : C} (p : B = B') (f : A ⟶ B') {G G' : D} (q : F.obj B' ⟶ G)
    (r : G ⟶ G') (s : F.obj A ⟶ G) (hq : F.map f ≫ q = s) :
    F.map (f ≫ eqToHom p.symm) ≫ (F.map (eqToIso p).hom ≫ (q ≫ r)) = s ≫ r := by
  subst p
  have hr : F.map f ≫ (q ≫ r) = s ≫ r := by rw [← Category.assoc, hq]
  simpa using hr

/-- The projections of a coherent module onto the terms of its completion are compatible with
every transition map of the inverse system, not only with the successor ones. -/
private lemma completionProjection_comp_map {Z : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian Z] (I : Z.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) {i j : ℕ}
    (h : j ≤ i) :
    completionProjection Z I M i ≫
        ((completionFunctor Z I).obj M).obj.map (homOfLE h).op =
      completionProjection Z I M j := by
  induction i, h using Nat.le_induction with
  | base =>
      have h0 : ∀ hj : j ≤ j, ((completionFunctor Z I).obj M).obj.map (homOfLE hj).op =
          𝟙 (((completionFunctor Z I).obj M).obj.obj (op j)) := fun hj =>
        (congrArg ((completionFunctor Z I).obj M).obj.map
            (Subsingleton.elim (homOfLE hj).op (𝟙 (op j)))).trans
          (((completionFunctor Z I).obj M).obj.map_id (op j))
      exact (congrArg (fun t => completionProjection Z I M j ≫ t) (h0 _)).trans
        (Category.comp_id _)
  | succ n hn ih =>
      have hfac : ∀ hj : j ≤ n + 1,
          ((completionFunctor Z I).obj M).obj.map (homOfLE hj).op =
            ((completionFunctor Z I).obj M).obj.map (homOfLE (Nat.le_succ n)).op ≫
              ((completionFunctor Z I).obj M).obj.map (homOfLE hn).op := fun hj =>
        (congrArg ((completionFunctor Z I).obj M).obj.map
            (Subsingleton.elim (homOfLE hj).op
              ((homOfLE (Nat.le_succ n)).op ≫ (homOfLE hn).op))).trans
          (((completionFunctor Z I).obj M).obj.map_comp _ _)
      refine Eq.trans
        (congrArg (fun t => completionProjection Z I M (n + 1) ≫ t) (hfac _)) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      exact (congrArg (fun t => t ≫ ((completionFunctor Z I).obj M).obj.map (homOfLE hn).op)
        (completionProjection_transition Z I M n)).trans ih

/-- `Stacks.Coherent.completionProjection_comp_map` for an arbitrary morphism of the index
category `ℕᵒᵖ`. -/
private lemma completionProjection_comp_map_op {Z : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian Z] (I : Z.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) {k l : ℕᵒᵖ}
    (h : k ⟶ l) :
    completionProjection Z I M k.unop ≫ ((completionFunctor Z I).obj M).obj.map h =
      completionProjection Z I M l.unop :=
  (congrArg (fun t => completionProjection Z I M k.unop ≫
      ((completionFunctor Z I).obj M).obj.map t)
    (Subsingleton.elim h (homOfLE (leOfHom h.unop)).op)).trans
    (completionProjection_comp_map I M (leOfHom h.unop))

/-- `Stacks.Algebraization.completionFunctor_map_quotient` indexed by an object of `ℕᵒᵖ`. -/
private lemma completionFunctor_map_quotient_unop {Z : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian Z] (I : Z.IdealSheafData)
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf} (a : M ⟶ N)
    (k : ℕᵒᵖ) :
    completionProjection Z I M k.unop ≫ ((completionFunctor Z I).map a).hom.app k =
      a.hom ≫ completionProjection Z I N k.unop :=
  completionFunctor_map_quotient Z I a k.unop

/-! ### The levelwise comparison -/

section Comparison

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (g : X ⟶ Y)
  (J : Y.IdealSheafData)

/-- The pullback of a coherent module, as an object of the category of coherent modules on the
source. -/
public abbrev pullbackCoherentModule
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ⟨(Scheme.Modules.pullback g).obj M.obj, AlgebraicGeometry.isCoherent_pullback g M.obj⟩

/-- **The pullback of the quotient `M / 𝒥 ⁿM` is the quotient `g^*M / ℐ ⁿ g^*M`.** This is
`Stacks.Coherent.exists_functor_idealPowerQuotient_iso` for termwise pullback, whose hypotheses
are right exactness — pullback is a left adjoint — and
`Stacks.Algebraization.pullback_idealPowerMultiple_comp_eq_zero_iff`. -/
public def pullbackIdealPowerQuotientIso (M : Y.Modules) (n : ℕ) :
    (Scheme.Modules.pullback g).obj (idealPowerQuotient J n M) ≅
      idealPowerQuotient (J.comap g) n ((Scheme.Modules.pullback g).obj M) :=
  (exists_functor_idealPowerQuotient_iso (Scheme.Modules.pullback g) J (J.comap g) n M
    (fun {_} φ => pullback_idealPowerMultiple_comp_eq_zero_iff g J n M φ)).choose

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
/-- `Stacks.Coherent.pullbackIdealPowerQuotientIso` is compatible with the two quotient
projections. -/
private lemma pullbackIdealPowerQuotientIso_spec (M : Y.Modules) (n : ℕ) :
    (Scheme.Modules.pullback g).map (cokernel.π (idealPowerMultiple J n M).ι) ≫
        (pullbackIdealPowerQuotientIso g J M n).hom =
      cokernel.π (idealPowerMultiple (J.comap g) n ((Scheme.Modules.pullback g).obj M)).ι :=
  (exists_functor_idealPowerQuotient_iso (Scheme.Modules.pullback g) J (J.comap g) n M
    (fun {_} φ => pullback_idealPowerMultiple_comp_eq_zero_iff g J n M φ)).choose_spec

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The pullback of a projection onto a term of a completion is an epimorphism: the projection is
one, and termwise pullback is a left adjoint. -/
private lemma epi_pullback_completionProjection
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (n : ℕ) :
    Epi (C := X.Modules) ((Scheme.Modules.pullback g).map (completionProjection Y J M n)) :=
  have hep : Epi (C := Y.Modules) (completionProjection Y J M n) :=
    epi_completionProjection J M n
  have hpe : (Scheme.Modules.pullback g).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (Scheme.Modules.pullbackPushforwardAdjunction g)
  @Functor.map_epi _ _ _ _ (Scheme.Modules.pullback g) hpe _ _
    (completionProjection Y J M n) hep

/-- **The comparison isomorphism at one level of the inverse system**: the pullback of the `n`-th
term of the completion of `M` is the `n`-th term of the completion of `g^*M`. -/
public def pullbackCompletionComparison
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (k : ℕᵒᵖ) :
    (Scheme.Modules.pullback g).obj (((completionFunctor Y J).obj M).obj.obj k) ≅
      ((completionFunctor X (J.comap g)).obj (pullbackCoherentModule g M)).obj.obj k :=
  (Scheme.Modules.pullback g).mapIso (eqToIso (completionFunctor_obj Y J M k.unop)) ≪≫
    pullbackIdealPowerQuotientIso g J M.obj (k.unop + 1) ≪≫
    eqToIso (completionFunctor_obj X (J.comap g) (pullbackCoherentModule g M) k.unop).symm

/-- **The levelwise comparison is normalised by the projections.** -/
public lemma pullbackCompletionComparison_projection
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (k : ℕᵒᵖ) :
    (Scheme.Modules.pullback g).map (completionProjection Y J M k.unop) ≫
        (pullbackCompletionComparison g J M k).hom =
      completionProjection X (J.comap g) (pullbackCoherentModule g M) k.unop :=
  map_comp_eqToHom_comparison (Scheme.Modules.pullback g)
    (completionFunctor_obj Y J M k.unop)
    (cokernel.π (idealPowerMultiple J (k.unop + 1) M.obj).ι)
    (pullbackIdealPowerQuotientIso g J M.obj (k.unop + 1)).hom
    (eqToHom (completionFunctor_obj X (J.comap g) (pullbackCoherentModule g M) k.unop).symm)
    (cokernel.π (idealPowerMultiple (J.comap g) (k.unop + 1)
      ((Scheme.Modules.pullback g).obj M.obj)).ι)
    (pullbackIdealPowerQuotientIso_spec g J M.obj (k.unop + 1))

/-- **The levelwise comparisons commute with the transition maps of the two inverse systems.**
Both sides are determined by their precomposition with the pullback of the projection from the
module, which is an epimorphism, and there they become the two ways of reading
`Stacks.Coherent.completionProjection_comp_map_op`. -/
public lemma pullbackCompletionComparison_naturality
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) {k l : ℕᵒᵖ}
    (h : k ⟶ l) :
    (Scheme.Modules.pullback g).map (((completionFunctor Y J).obj M).obj.map h) ≫
        (pullbackCompletionComparison g J M l).hom =
      (pullbackCompletionComparison g J M k).hom ≫
        ((completionFunctor X (J.comap g)).obj (pullbackCoherentModule g M)).obj.map h := by
  have := epi_pullback_completionProjection g J M k.unop
  rw [← cancel_epi ((Scheme.Modules.pullback g).map (completionProjection Y J M k.unop)),
    ← Category.assoc]
  erw [← (Scheme.Modules.pullback g).map_comp, completionProjection_comp_map_op,
    pullbackCompletionComparison_projection, ← Category.assoc,
    pullbackCompletionComparison_projection, completionProjection_comp_map_op]

/-- The levelwise form of `Stacks.Coherent.pullbackCompletionIso_naturality`. -/
private lemma pullbackCompletionComparison_naturality_module
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (a : M ⟶ N)
    (k : ℕᵒᵖ) :
    (Scheme.Modules.pullback g).map (((completionFunctor Y J).map a).hom.app k) ≫
        (pullbackCompletionComparison g J N k).hom =
      (pullbackCompletionComparison g J M k).hom ≫
        ((completionFunctor X (J.comap g)).map
          (ObjectProperty.homMk ((Scheme.Modules.pullback g).map a.hom) :
            pullbackCoherentModule g M ⟶ pullbackCoherentModule g N)).hom.app k := by
  have := epi_pullback_completionProjection g J M k.unop
  rw [← cancel_epi ((Scheme.Modules.pullback g).map (completionProjection Y J M k.unop)),
    ← Category.assoc]
  erw [← (Scheme.Modules.pullback g).map_comp, completionFunctor_map_quotient_unop,
    (Scheme.Modules.pullback g).map_comp, Category.assoc]
  rw [pullbackCompletionComparison_projection g J N k, ← Category.assoc,
    pullbackCompletionComparison_projection g J M k]
  exact (completionFunctor_map_quotient_unop (J.comap g)
    (ObjectProperty.homMk ((Scheme.Modules.pullback g).map a.hom) :
      pullbackCoherentModule g M ⟶ pullbackCoherentModule g N) k).symm

end Comparison

/-! ### The comparison isomorphism -/

/-- Pullback commutes with completion: `g^*(M^) ≅ (g^*M)^`. -/
public def pullbackCompletionIso {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (g : X ⟶ Y) (J : Y.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) :
    (coherentAdicPullback g J).obj ((Stacks.Algebraization.completionFunctor Y J).obj M) ≅
      (Stacks.Algebraization.completionFunctor X (J.comap g)).obj
        ⟨(Scheme.Modules.pullback g).obj M.obj, AlgebraicGeometry.isCoherent_pullback g M.obj⟩ :=
  ObjectProperty.isoMk _
    (NatIso.ofComponents (pullbackCompletionComparison g J M)
      (fun {_ _} h => pullbackCompletionComparison_naturality g J M h))

/-- The comparison is normalised by the projections: the pullback of the `n`-th projection
`M ⟶ M / 𝒥 ⁿ⁺¹M`, read through the comparison, is the `n`-th projection of `g^*M`. -/
public lemma pullbackCompletionIso_hom_app_projection {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (g : X ⟶ Y) (J : Y.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (n : ℕ) :
    (Scheme.Modules.pullback g).map
        (Stacks.Algebraization.completionProjection Y J M n) ≫
      (pullbackCompletionIso g J M).hom.hom.app (op n) =
      Stacks.Algebraization.completionProjection X (J.comap g)
        ⟨(Scheme.Modules.pullback g).obj M.obj,
          AlgebraicGeometry.isCoherent_pullback g M.obj⟩ n :=
  pullbackCompletionComparison_projection g J M (op n)

/-- Naturality of the comparison in the module. -/
public lemma pullbackCompletionIso_naturality {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (g : X ⟶ Y) (J : Y.IdealSheafData)
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (a : M ⟶ N) :
    ((coherentAdicPullback g J).map ((Stacks.Algebraization.completionFunctor Y J).map a)).hom ≫
        (pullbackCompletionIso g J N).hom.hom =
      (pullbackCompletionIso g J M).hom.hom ≫
        ((Stacks.Algebraization.completionFunctor X (J.comap g)).map
          (ObjectProperty.homMk ((Scheme.Modules.pullback g).map a.hom))).hom :=
  NatTrans.ext (funext fun k => pullbackCompletionComparison_naturality_module g J a k)

end Stacks.Coherent

end
