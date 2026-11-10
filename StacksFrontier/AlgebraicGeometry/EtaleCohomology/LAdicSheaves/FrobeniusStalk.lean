module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RationalStalkLeft

/-!
# The action of an endomorphism of a geometric point on the stalk of an ℓ-adic sheaf

An endomorphism `a` of a geometric point `x̄` of `X` acts on the étale stalk at `x̄` of any sheaf,
by the canonical stalk map of Tag 04FN. An ℓ-adic sheaf has one stalk at each finite level of
coefficients, and `a` acts on each of them; the content of this file is that these actions are
compatible with the transition maps between consecutive levels, so that they assemble into an
endomorphism of the ℓ-adic stalk `F_x̄ = lim_n F_{n, x̄}` over `ℤ_ℓ`, and hence, after extending
scalars, into an endomorphism of the rational stalk `ℚ_ℓ ⊗_{ℤ_ℓ} F_x̄` over `ℚ_ℓ`.

Both the level-`n` action and the level-`n` transition are maps out of the colimit over the
category of étale neighbourhoods of `x̄`: the action is `colimit.pre` along the restriction
functor on neighbourhoods, and the transition is the colimit of the whiskered transition of
sheaves followed by the comparison isomorphism for restriction of scalars. Their commutation is
therefore a statement about a colimit, proved by testing on the colimit injections; the two
lemmas of the first section are that computation in general form.

The geometric Frobenius at a closed point is such an endomorphism of a geometric point, so this
is what puts `π_x^*` on the rational stalk and makes the local factor
`det(1 - π_x^* T ^ (deg x) | F_x̄)` of Tag 03UX available.

## Main definitions

* `Stacks.EtaleCohomology.finiteLevelStalkEnd`: the action on one finite-level stalk.
* `Stacks.EtaleCohomology.LAdicSheaf.stalkEnd`: the induced `ℤ_ℓ`-linear endomorphism of the
  ℓ-adic stalk.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalStalkEnd`: its scalar extension, a `ℚ_ℓ`-linear
  endomorphism of the rational stalk.

## Main results

* `Stacks.EtaleCohomology.finiteLevelStalkEnd_transition`: the level-wise actions commute with
  the transitions, which is what makes `LAdicSheaf.stalkEnd` well defined.
* `Stacks.EtaleCohomology.LAdicSheaf.stalkProjection_stalkEnd`: the endomorphism of the ℓ-adic
  stalk is read off level by level.

## References

* [Stacks Project, Tag 03UQ](https://stacks.math.columbia.edu/tag/03UQ)
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-! ### Colimit injections against `colimit.pre` and a preservation isomorphism -/

section Colimits

variable {J : Type*} [Category J] {C : Type*} [Category C] {D : Type*} [Category D]
  [HasColimitsOfShape J C] [HasColimitsOfShape J D]

/-- Testing `colimit.pre A E ≫ colim.map β ≫ (preservesColimitIso R G).inv` on the colimit
injection at `j`: the injection is carried to the one at `E.obj j`, where `β` and the preservation
isomorphism act as they do on any injection. -/
lemma ι_pre_map_preservesColimitIso_inv (R : C ⥤ D) {A : J ⥤ D} {G : J ⥤ C}
    (β : A ⟶ G ⋙ R) (E : J ⥤ J) [PreservesColimit G R] (j : J) :
    colimit.ι (E ⋙ A) j ≫ colimit.pre A E ≫ colim.map β ≫ (preservesColimitIso R G).inv =
      β.app (E.obj j) ≫ R.map (colimit.ι G (E.obj j)) := by
  rw [colimit.ι_pre_assoc, colimit.ι_map_assoc, ι_preservesColimitIso_inv]

/-- Testing `(colim.map β ≫ (preservesColimitIso R G).inv) ≫ R.map p` on the colimit injection at
`j`, for an endomorphism `p` of `colimit G` whose effect on that injection is known to be `e`. -/
lemma ι_map_preservesColimitIso_inv_comp (R : C ⥤ D) {A : J ⥤ D} {G : J ⥤ C}
    (β : A ⟶ G ⋙ R) [PreservesColimit G R] (p : colimit G ⟶ colimit G) {j : J}
    {e : G.obj j ⟶ colimit G} (hp : colimit.ι G j ≫ p = e) :
    colimit.ι A j ≫ (colim.map β ≫ (preservesColimitIso R G).inv) ≫ R.map p =
      β.app j ≫ R.map e := by
  rw [Category.assoc, colimit.ι_map_assoc, ι_preservesColimitIso_inv_assoc, ← R.map_comp, hp]

end Colimits

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-! ### The action on the finite-level stalks -/

/-- The action of an endomorphism `a` of a geometric point `x̄` on the level-`n` stalk of an
ℓ-adic sheaf: the canonical map of stalk functors of Tag 04FN, at the level-`n` sheaf. -/
public def finiteLevelStalkEnd (F : LAdicSheaf B X ℓ) {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) (n : ℕ) :
    finiteLevelStalk B X ℓ F s n ⟶ finiteLevelStalk B X ℓ F s n :=
  (geometricPointStalkMap B X.1 X.property a
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).app (F.level n).obj

/-- The level-wise actions commute with the transitions between consecutive finite-level stalks.
Both the action and the transition are maps out of the colimit over the étale neighbourhoods of
`x̄`, and the identity is checked on the colimit injections. -/
public theorem finiteLevelStalkEnd_transition (F : LAdicSheaf B X ℓ) {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) (n : ℕ) :
    finiteLevelStalkEnd B X ℓ F a (n + 1) ≫ finiteLevelStalkTransition B X ℓ F s n =
      finiteLevelStalkTransition B X ℓ F s n ≫
        (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
          (finiteLevelStalkEnd B X ℓ F a n) := by
  change colimit.pre ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙
        (F.level (n + 1)).obj) (neighborhoodFunctor B X.1 X.property a).op ≫
      (colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op
          (F.transition n).hom) ≫
        (preservesColimitIso (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
          ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙
            (F.level n).obj)).inv) =
    (colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op
          (F.transition n).hom) ≫
        (preservesColimitIso (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
          ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙
            (F.level n).obj)).inv) ≫
      (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
        (colimit.pre ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙
          (F.level n).obj) (neighborhoodFunctor B X.1 X.property a).op)
  refine colimit.hom_ext fun j => ?_
  refine (ι_pre_map_preservesColimitIso_inv _ _ _ j).trans ?_
  symm
  refine ι_map_preservesColimitIso_inv_comp
    (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)) _ _ ?_
  exact colimit.ι_pre ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙
    (F.level n).obj) (neighborhoodFunctor B X.1 X.property a).op j

/-- The commutation of `finiteLevelStalkEnd` with the transitions, read on elements. -/
public theorem stalkTransition_finiteLevelStalkEnd (F : LAdicSheaf B X ℓ)
    {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) (n : ℕ)
    (y : finiteLevelStalk B X ℓ F s (n + 1)) :
    LAdicSheaf.stalkTransition B X ℓ F s n
        ((finiteLevelStalkEnd B X ℓ F a (n + 1)).hom y) =
      (finiteLevelStalkEnd B X ℓ F a n).hom
        (LAdicSheaf.stalkTransition B X ℓ F s n y) :=
  congrArg (fun g => g.hom y) (finiteLevelStalkEnd_transition B X ℓ F a n)

/-! ### The action on the ℓ-adic stalk and on the rational stalk -/

/-- The endomorphism of the ℓ-adic stalk at a geometric point `x̄` induced by an endomorphism `a`
of `x̄`: a compatible family of finite-level germs is sent to the family of its images under the
level-wise actions, which is again compatible by `finiteLevelStalkEnd_transition`. -/
public def LAdicSheaf.stalkEnd (F : LAdicSheaf B X ℓ) {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) :
    LAdicSheaf.stalk B X ℓ F s →ₗ[PadicInt ℓ] LAdicSheaf.stalk B X ℓ F s where
  toFun v :=
    ⟨fun n => (finiteLevelStalkEnd B X ℓ F a n).hom (v.1 n), fun n => by
      rw [stalkTransition_finiteLevelStalkEnd B X ℓ F a n (v.1 (n + 1)), v.2 n]⟩
  map_add' v w := Subtype.ext <| funext fun n =>
    map_add (finiteLevelStalkEnd B X ℓ F a n).hom (v.1 n) (w.1 n)
  map_smul' c v := Subtype.ext <| funext fun n =>
    map_smul (finiteLevelStalkEnd B X ℓ F a n).hom (PadicInt.toZModPow (n + 1) c) (v.1 n)

/-- The endomorphism of the ℓ-adic stalk is the level-wise action at every level. -/
public theorem LAdicSheaf.stalkProjection_stalkEnd (F : LAdicSheaf B X ℓ)
    {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) (n : ℕ)
    (v : LAdicSheaf.stalk B X ℓ F s) :
    LAdicSheaf.stalkProjection B X ℓ F s n (LAdicSheaf.stalkEnd B X ℓ F a v) =
      (finiteLevelStalkEnd B X ℓ F a n).hom
        (LAdicSheaf.stalkProjection B X ℓ F s n v) :=
  rfl

/-- The endomorphism of the rational stalk `ℚ_ℓ ⊗_{ℤ_ℓ} F_x̄` induced by an endomorphism of the
geometric point: the scalar extension to `ℚ_ℓ` of the endomorphism of the ℓ-adic stalk. -/
public def LAdicSheaf.rationalStalkEnd (F : LAdicSheaf B X ℓ) {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) :
    LAdicSheaf.rationalStalkLeft B X ℓ F s →ₗ[Padic ℓ] LAdicSheaf.rationalStalkLeft B X ℓ F s :=
  LinearMap.baseChange (Padic ℓ) (LAdicSheaf.stalkEnd B X ℓ F a)

/-- The endomorphism of the rational stalk on an element coming from the ℓ-adic stalk. -/
public theorem LAdicSheaf.rationalStalkEnd_tmul (F : LAdicSheaf B X ℓ)
    {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) (c : Padic ℓ)
    (v : LAdicSheaf.stalk B X ℓ F s) :
    LAdicSheaf.rationalStalkEnd B X ℓ F a (c ⊗ₜ[PadicInt ℓ] v) =
      c ⊗ₜ[PadicInt ℓ] LAdicSheaf.stalkEnd B X ℓ F a v :=
  LinearMap.baseChange_tmul _ _ _

end Stacks.EtaleCohomology

end
