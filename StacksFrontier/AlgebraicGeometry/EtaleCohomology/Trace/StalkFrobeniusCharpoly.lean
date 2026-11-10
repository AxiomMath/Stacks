module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPointExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyTracePowers
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkFiniteness

/-!
# The characteristic polynomial of the geometric Frobenius on stalks

The action `Stacks.EtaleCohomology.LAdicSheaf.rationalStalkEnd` of the geometric Frobenius on the
rational stalk of an ℓ-adic sheaf, under inverse image.

* Along a morphism `θ : s ⟶ t` of geometric points the finite-level stalk isomorphisms
  ([Stacks, Tag 04FN]) commute with the transitions, so the rational stalks at `s` and `t` have
  the same rank.
* For `g : X' ⟶ X` and a point `y` of `X'` whose residue field has as many elements as that of
  `x = g(y)`, the geometric Frobenius at `y` on the stalk of `g⁻¹ F` has the characteristic
  polynomial of the geometric Frobenius at `x` on the stalk of `F`: the powers have the same
  traces (`Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkEnd_eq_of_comm`, through the
  embedding of algebraic closures `Stacks.Frobenius.residueClosurePointHom`), the identity
  included, and Newton's identities conclude.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.finrank_rationalStalkLeft_eq_of_hom`.
* `Stacks.EtaleCohomology.LAdicSheaf.charpoly_rationalStalkFrobenius_inverseImage`.

## References

* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- Iterating commutes with `GeometricPoint.Hom.mapHom`. -/
theorem GeometricPoint.Hom.iterate_mapHom {X Y : Scheme.{u}} {x : GeometricPoint X}
    (a : GeometricPoint.Hom x x) (g : X ⟶ Y) (e : ℕ) :
    (a.iterate e).mapHom g = (a.mapHom g).iterate e := by
  refine GeometricPoint.Hom.ext' ?_
  induction e with
  | zero => rfl
  | succ e ih =>
      change (a.iterate e).hom ≫ a.hom = ((a.mapHom g).iterate e).hom ≫ a.hom
      change (a.iterate e).hom = ((a.mapHom g).iterate e).hom at ih
      rw [ih]

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-! ### Colimit injections against `colimit.pre` along a functor between index categories -/

section Colimits

variable {J J' : Type*} [Category J] [Category J'] {C : Type*} [Category C] {D : Type*}
  [Category D] [HasColimitsOfShape J C] [HasColimitsOfShape J D] [HasColimitsOfShape J' D]
  [HasColimitsOfShape J' C]

omit [HasColimitsOfShape J' C] in
/-- `colimit.pre A E ≫ colim.map β ≫ (preservesColimitIso R G).inv` on the injection at `j`, for
`E : J' ⥤ J` (the case `J' = J` is `Stacks.EtaleCohomology.ι_pre_map_preservesColimitIso_inv`). -/
lemma ι_pre_map_preservesColimitIso_inv_of_functor (R : C ⥤ D) {A : J ⥤ D} {G : J ⥤ C}
    (β : A ⟶ G ⋙ R) (E : J' ⥤ J) [PreservesColimit G R] (j : J') :
    colimit.ι (E ⋙ A) j ≫ colimit.pre A E ≫ colim.map β ≫ (preservesColimitIso R G).inv =
      β.app (E.obj j) ≫ R.map (colimit.ι G (E.obj j)) := by
  rw [colimit.ι_pre_assoc, colimit.ι_map_assoc, ι_preservesColimitIso_inv]

/-- `(colim.map β ≫ (preservesColimitIso R G).inv) ≫ R.map p` on the injection at `j`, for a map
`p` out of `colimit G` whose effect on that injection is `e` (the case of an endomorphism is
`Stacks.EtaleCohomology.ι_map_preservesColimitIso_inv_comp`). -/
lemma ι_map_preservesColimitIso_inv_comp_of_hom (R : C ⥤ D) {A : J' ⥤ D} {G : J' ⥤ C}
    (β : A ⟶ G ⋙ R) [PreservesColimit G R] {Z : C} (p : colimit G ⟶ Z) {j : J'}
    {e : G.obj j ⟶ Z} (hp : colimit.ι G j ≫ p = e) :
    colimit.ι A j ≫ (colim.map β ≫ (preservesColimitIso R G).inv) ≫ R.map p =
      β.app j ≫ R.map e := by
  rw [Category.assoc, colimit.ι_map_assoc, ι_preservesColimitIso_inv_assoc, ← R.map_comp, hp]

end Colimits

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fact ℓ.Prime]

section Invertible

variable (X : B.Scheme) [IsNoetherian X.1]

/-- **The finite-level stalk isomorphisms along a morphism of geometric points commute with the
transitions**, as in `Stacks.EtaleCohomology.finiteLevelStalkEnd_transition` for endomorphisms. -/
theorem finiteLevelStalkPointIso_transition (F : LAdicSheaf B X ℓ) {s t : GeometricPoint X.1}
    (θ : GeometricPoint.Hom s t) (n : ℕ) :
    (finiteLevelStalkPointIso B X ℓ F θ (n + 1)).hom ≫ finiteLevelStalkTransition B X ℓ F s n =
      finiteLevelStalkTransition B X ℓ F t n ≫
        (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
          (finiteLevelStalkPointIso B X ℓ F θ n).hom := by
  change colimit.pre ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙
        (F.level (n + 1)).obj) (neighborhoodFunctor B X.1 X.property θ).op ≫
      (colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op
          (F.transition n).hom) ≫
        (preservesColimitIso (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
          ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙
            (F.level n).obj)).inv) =
    (colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B X.1 X.property t)).op
          (F.transition n).hom) ≫
        (preservesColimitIso (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
          ((Functor.Elements.π (geometricPointFiber B X.1 X.property t)).op ⋙
            (F.level n).obj)).inv) ≫
      (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
        (colimit.pre ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙
          (F.level n).obj) (neighborhoodFunctor B X.1 X.property θ).op)
  apply colimit.hom_ext
  intro j
  have h1 := ι_pre_map_preservesColimitIso_inv_of_functor
      (R := ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
      (A := (Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙
        (F.level (n + 1)).obj)
      (G := (Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙ (F.level n).obj)
      (β := Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op
        (F.transition n).hom)
      (E := (neighborhoodFunctor B X.1 X.property θ).op) (j := j)
  have h2 := ι_map_preservesColimitIso_inv_comp_of_hom
      (R := ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
      (A := (Functor.Elements.π (geometricPointFiber B X.1 X.property t)).op ⋙
        (F.level (n + 1)).obj)
      (G := (Functor.Elements.π (geometricPointFiber B X.1 X.property t)).op ⋙ (F.level n).obj)
      (β := Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber B X.1 X.property t)).op
        (F.transition n).hom)
      (p := colimit.pre ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙
        (F.level n).obj) (neighborhoodFunctor B X.1 X.property θ).op)
      (hp := colimit.ι_pre ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op ⋙
        (F.level n).obj) (neighborhoodFunctor B X.1 X.property θ).op j)
  exact h1.trans h2.symm

/-- **The ℓ-adic stalks at the two ends of a morphism of geometric points have the same rank**:
the finite-level stalk isomorphisms along it ([Stacks, Tag 04FN]) commute with the transitions,
so they induce an isomorphism of the ℓ-adic stalks. -/
theorem LAdicSheaf.finrank_rationalStalkLeft_eq_of_hom (F : LAdicSheaf B X ℓ)
    {s t : GeometricPoint X.1} (θ : GeometricPoint.Hom s t) :
    Module.finrank (Padic ℓ) (LAdicSheaf.rationalStalkLeft B X ℓ F t) =
      Module.finrank (Padic ℓ) (LAdicSheaf.rationalStalkLeft B X ℓ F s) := by
  let E := fun n => finiteLevelStalkPointIso B X ℓ F θ n
  have hbij : ∀ n, Function.Bijective (E n).hom.hom := fun n =>
    ConcreteCategory.bijective_of_isIso (E n).hom
  have hcomm : ∀ n (y : finiteLevelStalk B X ℓ F t (n + 1)),
      LAdicSheaf.stalkTransition B X ℓ F s n ((E (n + 1)).hom.hom y) =
        (E n).hom.hom (LAdicSheaf.stalkTransition B X ℓ F t n y) := fun n y =>
    congrArg (fun g => g.hom y) (finiteLevelStalkPointIso_transition B ℓ X F θ n)
  let L : LAdicSheaf.stalk B X ℓ F t →ₗ[PadicInt ℓ] LAdicSheaf.stalk B X ℓ F s :=
    { toFun := fun v => ⟨fun n => (E n).hom.hom (v.1 n), fun n => by
        rw [hcomm n (v.1 (n + 1)), v.2 n]⟩
      map_add' := fun v w => Subtype.ext (funext fun n => map_add (E n).hom.hom (v.1 n) (w.1 n))
      map_smul' := fun c v => Subtype.ext (funext fun n =>
        map_smul (E n).hom.hom (PadicInt.toZModPow (n + 1) c) (v.1 n)) }
  have hL : Function.Bijective L := by
    refine ⟨fun v w hvw => Subtype.ext (funext fun n => (hbij n).1 ?_), fun w => ?_⟩
    · exact congrArg (fun z => z.1 n) hvw
    · let v : ∀ n, finiteLevelStalk B X ℓ F t n := fun n => ((hbij n).2 (w.1 n)).choose
      have hv : ∀ n, (E n).hom.hom (v n) = w.1 n := fun n => ((hbij n).2 (w.1 n)).choose_spec
      refine ⟨⟨v, fun n => (hbij n).1 ?_⟩, Subtype.ext (funext hv)⟩
      rw [← hcomm n (v (n + 1)), hv, hv]
      exact w.2 n
  exact ((LinearEquiv.ofBijective L hL).baseChange (PadicInt ℓ) (Padic ℓ) _ _).finrank_eq

end Invertible

section InverseImage

variable {X' X : B.Scheme} [IsNoetherian X'.1] [IsNoetherian X.1] (g : X' ⟶ X)

/-- **The geometric Frobenius at a point above a point with as many elements in its residue
field has the same characteristic polynomial on the stalks of `g⁻¹ F` and of `F`.** -/
theorem LAdicSheaf.charpoly_rationalStalkFrobenius_inverseImage (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (y : X'.1) (hy : Finite (X'.1.residueField y))
    (hx : Finite (X.1.residueField ((B.inclusion.map g).base y)))
    (he : Nat.card (X'.1.residueField y) =
      Nat.card (X.1.residueField ((B.inclusion.map g).base y))) :
    (LAdicSheaf.rationalStalkFrobenius B X' ℓ (LAdicSheaf.inverseImage g F) y hy).charpoly =
      (LAdicSheaf.rationalStalkFrobenius B X ℓ F ((B.inclusion.map g).base y) hx).charpoly := by
  have := hy
  have := hx
  have : Finite ((B.inclusion.obj X').residueField y) := hy
  have : Finite ((B.inclusion.obj X).residueField ((B.inclusion.map g).base y)) := hx
  have hcomm := frobeniusPointHom_iterate_comm (B.inclusion.map g) y 0
    (by rw [zero_add, pow_one]; exact he)
  have htr : ∀ e : ℕ, LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkEnd B X' ℓ
      (LAdicSheaf.inverseImage g F) ((frobeniusPointHom X'.1 y).iterate e)) =
      LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkEnd B X ℓ F
        ((frobeniusPointHom X.1 ((B.inclusion.map g).base y)).iterate e)) := fun e => by
    rw [trace_inverseImage_rationalStalkEnd, GeometricPoint.Hom.iterate_mapHom]
    exact LAdicSheaf.trace_rationalStalkEnd_eq_of_comm B X ℓ F
      (residueClosurePointHom (B.inclusion.map g) y) _ _
      ((residueClosurePointHom (B.inclusion.map g) y).comp_iterate_of_comp_eq hcomm e)
  refine charpoly_eq_of_trace_pow_eq _ _ ?_ fun k hk => ?_
  · rw [(rationalInverseImageStalkEquiv B g F (geometricPointAt X'.1 y)).finrank_eq]
    exact (LAdicSheaf.finrank_rationalStalkLeft_eq_of_hom B ℓ X F
      (residueClosurePointHom (B.inclusion.map g) y)).symm
  · obtain ⟨e, rfl⟩ : ∃ e, k = e + 1 := ⟨k - 1, by omega⟩
    change LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkEnd B X' ℓ
        (LAdicSheaf.inverseImage g F) (frobeniusPointHom X'.1 y) ^ (e + 1)) =
      LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkEnd B X ℓ F
        (frobeniusPointHom X.1 ((B.inclusion.map g).base y)) ^ (e + 1))
    rw [← LAdicSheaf.rationalStalkEnd_iterate, ← LAdicSheaf.rationalStalkEnd_iterate]
    exact htr e

end InverseImage

end Stacks.EtaleCohomology
