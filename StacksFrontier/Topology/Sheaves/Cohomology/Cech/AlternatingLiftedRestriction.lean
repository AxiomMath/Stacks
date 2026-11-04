module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplexFunctor

/-!
# The alternating Čech complex of a family read on another space

Let `X` and `Y` be topological spaces, let `U : Fin r → Opens X` be a finite family of opens of
`X` and let `V : ULift (Fin r) → Opens Y` be a family of opens of `Y` indexed by a lift of the
same index type.  Let `T : Opens Y ⥤ Opens X` be a functor on the lattices of opens carrying
every intersection `V_{i₀…i_p}` to the corresponding intersection `U_{i₀…i_p}`.  Then the
alternating Čech complex of `U` with coefficients in an abelian presheaf `F` on `X` is
canonically isomorphic to the alternating Čech complex of `V` with coefficients in the presheaf
`Tᵒᵖ ⋙ F` on `Y`, naturally in `F`: both are built from the same groups of sections.

This is the comparison that identifies the Čech complex of a covering of an open `U ⊆ X` by
opens of `X` with the Čech complex of the induced covering of the open subspace `U`.

## Main definitions

* `Stacks.Cech.alternatingSubgroupLiftedEquiv`: the isomorphism on the groups of alternating
  cochains in a fixed degree.
* `Stacks.Cech.alternatingCechComplexLiftedIso`: the isomorphism of alternating Čech complexes.
* `Stacks.Cech.alternatingCechComplexFunctorLiftedIso`: the same, naturally in the coefficient
  presheaf.
* `Stacks.Cech.alternatingCechTotalComplexFunctorLiftedIso`: the induced isomorphism of total
  alternating Čech complexes of a complex of abelian presheaves.

## Implementation notes

The index type is lifted because the unbounded Čech theory of Tags 08C0 and 08C1 is stated for
a family indexed by a type in the universe of the space, while a finite family `U₁, …, U_r` is
indexed by `Fin r`.  Both Čech complexes then take values in abelian groups of the common
universe, since `max 0 u` and `max u u` are both `u`.

A tuple of lifted indices is injective exactly when the underlying tuple is, and the two
intersections attached to a tuple are related by the given isomorphism, so the alternating
conditions transport.  The identifications of sections used in the two conditions and in the
differential are maps between the same pair of opens, and `Opens X` is a partial order, so they
agree without further argument.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u

namespace Stacks.Cech

open CechCochains

variable {X Y : TopCat.{u}} {r : ℕ} (U : Fin r → Opens X)
    (V : ULift.{u} (Fin r) → Opens Y) (T : Opens Y ⥤ Opens X)
    (e : ∀ (p : ℕ) (i : Fin (p + 1) → ULift.{u} (Fin r)),
      T.obj (inter V i) ≅ inter U (fun k ↦ (i k).down))

/-- Two restriction maps of an abelian presheaf between the same two opens agree: `Opens X` is
a partial order, so it has at most one morphism between any two objects. -/
theorem map_eq_map_of_opens {X : TopCat.{u}} (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {P Q : (Opens X)ᵒᵖ} (a b : P ⟶ Q) : F.map a = F.map b :=
  congrArg F.map (Subsingleton.elim a b)

/-- Two composites of restriction maps of an abelian presheaf with the same source and target
agree. -/
theorem map_comp_eq_map_comp_of_opens {X : TopCat.{u}} (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {P Q R S : (Opens X)ᵒᵖ} (a : P ⟶ Q) (b : Q ⟶ R) (c : P ⟶ S) (d : S ⟶ R) :
    F.map a ≫ F.map b = F.map c ≫ F.map d :=
  ((F.map_comp a b).symm.trans (map_eq_map_of_opens F (a ≫ b) (c ≫ d))).trans (F.map_comp c d)

/-- A tuple of lifted indices is injective as soon as the underlying tuple is. -/
theorem injective_of_injective_down {p : ℕ} {i : Fin (p + 1) → ULift.{u} (Fin r)}
    (h : Function.Injective fun k ↦ (i k).down) : Function.Injective i :=
  fun _ _ hab ↦ h (congrArg ULift.down hab)

/-- A tuple of indices is injective as soon as its lift is. -/
theorem injective_of_injective_up {p : ℕ} {i : Fin (p + 1) → Fin r}
    (h : Function.Injective fun k ↦ (⟨i k⟩ : ULift.{u} (Fin r))) : Function.Injective i :=
  fun _ _ hab ↦ h (congrArg ULift.up hab)

variable (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- **The groups of alternating Čech cochains of the two families agree.**  A cochain for `U`
with coefficients in `F` is sent to the cochain for `V` with coefficients in `Tᵒᵖ ⋙ F` whose
value at a tuple `i` is the value of the original at the underlying tuple, read on
`T(V_{i₀…i_p})` along the given identification. -/
def alternatingSubgroupLiftedEquiv (p : ℕ) :
    alternatingSubgroup U F p ≃+ alternatingSubgroup V (T.op ⋙ F) p where
  toFun s := ⟨fun i ↦ F.map (e p i).hom.op (s.1 fun k ↦ (i k).down), by
    refine ⟨fun i hi ↦ ?_, fun i j k hjk ↦ ?_⟩
    · change F.map (e p i).hom.op (s.1 fun k ↦ (i k).down) = 0
      rw [s.2.1 _ (fun h ↦ hi (injective_of_injective_down h)), map_zero]
    · change F.map (e p (i ∘ Equiv.swap j k)).hom.op
          (s.1 ((fun l ↦ (i l).down) ∘ Equiv.swap j k)) =
        - (T.op ⋙ F).map _ (F.map (e p i).hom.op (s.1 fun l ↦ (i l).down))
      rw [s.2.2 (fun l ↦ (i l).down) j k hjk, map_neg]
      congr 1
      change (F.map _ ≫ F.map _) (s.1 fun l ↦ (i l).down) =
        (F.map _ ≫ F.map _) (s.1 fun l ↦ (i l).down)
      exact ConcreteCategory.congr_hom (map_comp_eq_map_comp_of_opens F _ _ _ _) _⟩
  invFun s := ⟨fun i ↦ F.map (e p (fun k ↦ ⟨i k⟩)).inv.op (s.1 fun k ↦ ⟨i k⟩), by
    refine ⟨fun i hi ↦ ?_, fun i j k hjk ↦ ?_⟩
    · change F.map (e p (fun k ↦ ⟨i k⟩)).inv.op (s.1 fun k ↦ ⟨i k⟩) = 0
      rw [s.2.1 _ (fun h ↦ hi (injective_of_injective_up h)), map_zero]
    · change F.map (e p (fun l ↦ ⟨i (Equiv.swap j k l)⟩)).inv.op
          (s.1 ((fun l ↦ (⟨i l⟩ : ULift.{u} (Fin r))) ∘ Equiv.swap j k)) =
        - F.map _ (F.map (e p (fun l ↦ ⟨i l⟩)).inv.op (s.1 fun l ↦ ⟨i l⟩))
      rw [s.2.2 (fun l ↦ (⟨i l⟩ : ULift.{u} (Fin r))) j k hjk, map_neg]
      congr 1
      change (F.map _ ≫ F.map _) (s.1 fun l ↦ (⟨i l⟩ : ULift.{u} (Fin r))) =
        (F.map _ ≫ F.map _) (s.1 fun l ↦ (⟨i l⟩ : ULift.{u} (Fin r)))
      exact ConcreteCategory.congr_hom (map_comp_eq_map_comp_of_opens F _ _ _ _) _⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    change (F.map (e p (fun k ↦ ⟨i k⟩)).hom.op ≫
      F.map (e p (fun k ↦ ⟨i k⟩)).inv.op) (s.1 i) = s.1 i
    rw [← F.map_comp, ← op_comp, Iso.inv_hom_id, op_id, F.map_id]
    rfl
  right_inv s := by
    apply Subtype.ext
    funext i
    change (F.map (e p i).inv.op ≫ F.map (e p i).hom.op) (s.1 i) = s.1 i
    rw [← F.map_comp, ← op_comp, Iso.hom_inv_id, op_id, F.map_id]
    rfl
  map_add' _ _ := Subtype.ext <| funext fun _ ↦ map_add _ _ _

/-- **The alternating Čech complexes of the two families agree.** -/
noncomputable def alternatingCechComplexLiftedIso :
    alternatingCechComplex U F ≅ alternatingCechComplex V (T.op ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ (alternatingSubgroupLiftedEquiv U V T e F p).toAddCommGrpIso)
    (fun p q hpq ↦ by
      obtain rfl : p + 1 = q := hpq
      rw [alternatingCechComplex_d, alternatingCechComplex_d]
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      apply Subtype.ext
      funext i
      change (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        restr (T.op ⋙ F) (inter_le_omit V i j)
          (F.map (e p (i ∘ j.succAbove)).hom.op
            (s.1 fun l ↦ (i (j.succAbove l)).down))) =
        F.map (e (p + 1) i).hom.op (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          restr F (inter_le_omit U (fun l ↦ (i l).down) j)
            (s.1 ((fun l ↦ (i l).down) ∘ j.succAbove)))
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_zsmul]
      congr 1
      change (F.map _ ≫ F.map _) (s.1 fun l ↦ (i (j.succAbove l)).down) =
        (F.map _ ≫ F.map _) (s.1 fun l ↦ (i (j.succAbove l)).down)
      exact ConcreteCategory.congr_hom (map_comp_eq_map_comp_of_opens F _ _ _ _) _)

/-- **The alternating Čech complexes of the two families agree, naturally in the coefficient
presheaf.** -/
noncomputable def alternatingCechComplexFunctorLiftedIso :
    alternatingCechComplexFunctor U ≅
      (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj T.op ⋙
        alternatingCechComplexFunctor V :=
  NatIso.ofComponents (alternatingCechComplexLiftedIso U V T e) (by
    intro F G a
    ext p s
    exact Subtype.ext <| funext fun i ↦ ConcreteCategory.congr_hom
      (a.naturality (e p i).hom.op).symm (s.1 fun l ↦ (i l).down))

/-- **The total alternating Čech complexes of the two families agree**, for a complex of
abelian presheaves on `X` and the corresponding complex of abelian presheaves on `Y`. -/
noncomputable def alternatingCechTotalComplexFunctorLiftedIso :
    alternatingCechTotalComplexFunctor U ≅
      ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
          T.op).mapHomologicalComplex (up ℤ) ⋙
        alternatingCechTotalComplexFunctor V := by
  let W := (Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj T.op
  letI : W.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  let B := embeddingUpNat.extendFunctor AddCommGrpCat.{u}
  letI : (W ⋙ alternatingCechComplexFunctor V ⋙ B).PreservesZeroMorphisms := inferInstance
  let e' := NatIso.mapHomologicalComplex
    (Functor.isoWhiskerRight (alternatingCechComplexFunctorLiftedIso U V T e) B) (up ℤ)
  exact Functor.isoWhiskerRight e'
    (HomologicalComplex₂.flipFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) ⋙
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ))

end Stacks.Cech

end
