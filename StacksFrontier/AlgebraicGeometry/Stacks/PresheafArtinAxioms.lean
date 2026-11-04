module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableFromDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability
public import StacksFrontier.CategoryTheory.Sites.Stack.PresheafElementsStack
public import StacksFrontier.Deformation.Artin.LimitPreserving

/-!
# Artin's axioms for a functor and for its category fibred in sets (Stacks 07XZ)

Let `F` be a set-valued presheaf on the big fppf site of `S` and `𝒮_F` the category fibred in
sets attached to it (`AlgebraicGeometry.Stack.fibredCategory`, Stacks 04SU / 0458). Artin's
axioms for `𝒮_F` translate into conditions on `F` (Stacks 07XZ):

* axiom [0]: if `F` is a sheaf for a topology `J`, then `𝒮_F` is a stack in groupoids for `J`;
* the diagonal: if the diagonal `F ⟶ F × F` is representable by algebraic spaces, then so is the
  diagonal of `𝒮_F` (in the sense of Stacks 045G);
* axiom [1]: if `F` is limit preserving in the sense of Stacks 049J, then `𝒮_F` is limit
  preserving in the sense of Stacks 07XL.

## Main results

* `AlgebraicGeometry.Stack.isStackInGroupoids_fibredCategory_of_isSheaf`: axiom [0].
* `AlgebraicGeometry.Stack.eq_associatedMap_natTransOfBasedFunctor`: every 1-morphism between
  the categories fibred in sets of two presheaves is the one attached to a map of presheaves.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_fibredCategory`: the diagonal.
* `AlgebraicGeometry.Stack.isLimitPreserving_fibredCategory`: axiom [1].

## References

* [Stacks Project, Tag 07XZ](https://stacks.math.columbia.edu/tag/07XZ)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The category fibred in sets attached to a presheaf which is a sheaf for a topology `J` is a
stack in groupoids for `J`, at every descent universe (axiom [0] of Stacks 07XZ). -/
theorem isStackInGroupoids_fibredCategory_of_isSheaf
    {J : GrothendieckTopology (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : Presheaf.IsSheaf J F) :
    (fibredCategory B S hS F).val.p.IsStackInGroupoids.{w} J :=
  (PresheafOfCategories.isStackInSetoids_of_equivalenceOver_discreteProjection F J hF
    (StacksRepresentableCFG.EquivalenceOver.refl _)).isStack.isStackInGroupoids
    (fibredCategory B S hS F).isFiberedInGroupoids

/-- A 1-morphism between the categories fibred in sets of two presheaves is the one attached by
Stacks 0458 to the map of presheaves `CategoryTheory.PresheafOfCategories.natTransOfBasedFunctor`
it induces. -/
theorem eq_associatedMap_natTransOfBasedFunctor {G F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (θ : (fibredCategory B S hS G).val ⥤ᵇ (fibredCategory B S hS F).val) :
    θ = (associatedMap B S hS
      (PresheafOfCategories.natTransOfBasedFunctor θ.toFunctor θ.w)).1.hom := by
  have : (fibredCategory B S hS F).val.p.IsFiberedInSets :=
    inferInstanceAs (PresheafOfCategories.discreteProjection F).IsFiberedInSets
  refine BasedCategory.BasedFunctor.ext' ?_
  refine Functor.IsFiberedInSets.eq_of_obj_eq
    (fibredCategory B S hS G).val.p (fibredCategory B S hS F).val.p _ _
    θ.w (associatedMap B S hS _).1.hom.w (fun x => ?_)
  exact (obj_eq_mk_natTransOfBasedFunctor θ x).trans (associatedMap_obj B S hS _ x).symm

/-- A 1-morphism `𝒮_G ⟶ 𝒮_F` between the categories fibred in sets of two presheaves is
representable by algebraic spaces as soon as the map of presheaves `G ⟶ F` it induces is. -/
theorem isRepresentableByAlgebraicSpaces_of_natTransOfBasedFunctor
    {G F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (θ : (fibredCategory B S hS G).val ⥤ᵇ (fibredCategory B S hS F).val)
    (h : Space.IsRepresentableByAlgebraicSpaces B S hS
      (PresheafOfCategories.natTransOfBasedFunctor θ.toFunctor θ.w)) :
    IsRepresentableByAlgebraicSpaces B S hS θ := by
  have key := eq_associatedMap_natTransOfBasedFunctor B S hS θ
  generalize PresheafOfCategories.natTransOfBasedFunctor θ.toFunctor θ.w = a at h key
  subst key
  exact (isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS a).1 h

/-- If the diagonal `F ⟶ F × F` of a presheaf is representable by algebraic spaces, then every
1-morphism `(Sch/U) ⟶ 𝒮_F` is representable by algebraic spaces (condition (3) of
Stacks 045G). -/
theorem isRepresentableFromSchemes_fibredCategory {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hdiag : Space.IsRepresentableByAlgebraicSpaces B S hS (diag F)) :
    IsRepresentableFromSchemes B S hS (fibredCategory B S hS F) := by
  intro U x
  let e := PresheafOfCategories.sliceElementsEquivalenceOver U
  have : Functor.IsEquivalence
      (⟨e.inv.functor, e.inv.w⟩ : (fibredCategory B S hS (yoneda.obj U)).val ⥤ᵇ
        (schemeFibredCategory B S hS U).val).toFunctor :=
    e.isEquivalence_inv_functor
  refine isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst
    (f := BasedFunctor.comp ⟨e.inv.functor, e.inv.w⟩ x) (f' := x)
    (fun V y hy => (nonempty_equivalenceOver_fst_of_equivalence_source B S hS
      (𝒳' := fibredCategory B S hS (yoneda.obj U)) ⟨e.inv.functor, e.inv.w⟩ x V y hy).map
      StacksRepresentableCFG.EquivalenceOver.symm) ?_
  exact isRepresentableByAlgebraicSpaces_of_natTransOfBasedFunctor B S hS
    (BasedFunctor.comp ⟨e.inv.functor, e.inv.w⟩ x)
    (Space.isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag
      (isAlgebraicSpace_yoneda B S hS U) _)

/-- If the diagonal `F ⟶ F × F` of a presheaf on the big fppf site of `S` is representable by
algebraic spaces, then so is the diagonal of `𝒮_F`. -/
theorem hasRepresentableDiagonal_fibredCategory {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hdiag : Space.IsRepresentableByAlgebraicSpaces B S hS (diag F)) :
    HasRepresentableDiagonal B S hS (fibredCategory B S hS F) :=
  (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS _).2
    (isAlgebraicSpaceIsomPresheaf_of_isRepresentableFromSchemes B S hS _
      (isRepresentableFromSchemes_fibredCategory B S hS hdiag))

section LimitPreserving

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Two morphisms of the category fibred in sets of a presheaf lying over the same morphism of the
site are equal. -/
theorem hom_eq_of_isHomLift_fibredCategory {X Y : (fibredCategory B S hS F).val.obj}
    {U V : BigFppfOver B S hS} (f : U ⟶ V) (φ ψ : X ⟶ Y)
    [(fibredCategory B S hS F).val.p.IsHomLift f φ]
    [(fibredCategory B S hS F).val.p.IsHomLift f ψ] : φ = ψ := by
  have := faithful_fibredCategory_projection F
  apply (fibredCategory B S hS F).val.p.map_injective
  rw [IsHomLift.fac' (fibredCategory B S hS F).val.p f φ,
    IsHomLift.fac' (fibredCategory B S hS F).val.p f ψ]

/-- The morphism of the category fibred in sets of `F` over `f : V ⟶ W` from `(V, s)` to
`(W, t)`, for `s` the restriction of `t` along `f`. -/
def fibredCategoryHomMk {V W : BigFppfOver B S hS} (f : V ⟶ W) {s : F.obj (op V)}
    {t : F.obj (op W)} (h : s = F.map f.op t) :
    (⟨V, Discrete.mk s⟩ : (fibredCategory B S hS F).val.obj) ⟶ ⟨W, Discrete.mk t⟩ :=
  ⟨f, Discrete.eqToHom h⟩

/-- The morphism `fibredCategoryHomMk f h` lies over `f`. -/
instance isHomLift_fibredCategoryHomMk {V W : BigFppfOver B S hS} (f : V ⟶ W)
    {s : F.obj (op V)} {t : F.obj (op W)} (h : s = F.map f.op t) :
    (fibredCategory B S hS F).val.p.IsHomLift f (fibredCategoryHomMk B S hS f h) :=
  IsHomLift.map (fibredCategory B S hS F).val.p (fibredCategoryHomMk B S hS f h)

/-- A morphism of the category fibred in sets of `F` lying over `f` identifies the element named
by its source with the restriction along `f` of the element named by its target. -/
theorem eq_map_of_isHomLift_fibredCategory {V W : BigFppfOver B S hS} (f : V ⟶ W)
    {s : F.obj (op V)} {t : F.obj (op W)}
    (φ : (⟨V, Discrete.mk s⟩ : (fibredCategory B S hS F).val.obj) ⟶ ⟨W, Discrete.mk t⟩)
    [(fibredCategory B S hS F).val.p.IsHomLift f φ] : s = F.map f.op t :=
  PresheafOfCategories.elementOf_eq_map (P := F) (X := ⟨V, Discrete.mk s⟩)
    (Y := ⟨W, Discrete.mk t⟩) (V := V) (W := W) rfl rfl f φ
    (inferInstanceAs ((fibredCategory B S hS F).val.p.IsHomLift f φ))

/-- The category fibred in sets attached to a presheaf which is limit preserving in the sense of
Stacks 049J (for index categories in the universe of the site) is limit preserving in the sense
of Stacks 07XL (axiom [1] of Stacks 07XZ). -/
theorem isLimitPreserving_fibredCategory
    (hF : AlgebraicGeometry.LimitPreserving.{u, u, u, u} (BigFppfOver.toScheme B S hS) F) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS (fibredCategory B S hS F) := by
  intro I _ _ D c hc
  let : (fibredCategory B S hS F).val.p.IsFibered := (fibredCategory B S hS F).2.isFibered
  have hp : (fibredCategory B S hS F).val.p.IsFiberedInGroupoids := (fibredCategory B S hS F).2
  let D' := D ⋙ BigAffineFppf.inclusion B S hS
  let c' := (BigAffineFppf.inclusion B S hS).mapCone c
  obtain ⟨hcol⟩ := hF I D' c' hc (fun i => (D.obj i).property) c.pt.property
  have hcolEq : ∀ (i : I) (a b : F.obj (op (D'.obj i))),
      F.map (c'.π.app i).op a = F.map (c'.π.app i).op b →
        ∃ (k : I) (s : k ⟶ i), F.map (D'.map s).op a = F.map (D'.map s).op b := by
    intro i a b hab
    obtain ⟨j, f, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hcol (i := op i) a b).1 hab
    exact ⟨j.unop, f.unop, hf⟩
  refine { faithful := Deformation.Artin.faithful_of_descentEq _ hp D' c' ?_,
           full := Deformation.Artin.full_of_descentHom _ hp D' c' ?_,
           essSurj := Deformation.Artin.essSurj_of_descentObj _ hp D' c' ?_ }
  · intro i xi yi x δ hδ ψ ψ' hψ hψ' _
    have hψψ' : ψ = ψ' := hom_eq_of_isHomLift_fibredCategory B S hS (𝟙 (D'.obj i)) ψ ψ'
    refine ⟨i, 𝟙 i, xi, 𝟙 xi.1, ?_, by rw [hψψ']⟩
    simpa only [D'.map_id] using
      IsHomLift.id (p := (fibredCategory B S hS F).val.p) xi.2
  · intro i xi yi x y δ ε hδ hε φ hφ
    obtain ⟨⟨bi, ⟨a⟩⟩, hbi⟩ := xi
    obtain ⟨⟨bj, ⟨b⟩⟩, hbj⟩ := yi
    obtain ⟨⟨bx, ⟨s⟩⟩, hbx⟩ := x
    obtain ⟨⟨by', ⟨t⟩⟩, hby⟩ := y
    change bi = _ at hbi
    change bj = _ at hbj
    change bx = _ at hbx
    change by' = _ at hby
    subst hbi hbj hbx hby
    have hs : s = F.map (c'.π.app i).op a :=
      eq_map_of_isHomLift_fibredCategory B S hS (c'.π.app i) δ
    have ht : t = F.map (c'.π.app i).op b :=
      eq_map_of_isHomLift_fibredCategory B S hS (c'.π.app i) ε
    have hst : s = t := by
      simpa using eq_map_of_isHomLift_fibredCategory B S hS (𝟙 c'.pt) φ
    obtain ⟨k, r, hr⟩ := hcolEq i a b (hs.symm.trans (hst.trans ht))
    have hk : s = F.map (c'.π.app k).op (F.map (D'.map r).op a) := by
      rw [hs, ← FunctorToTypes.map_comp_apply, ← op_comp, c'.w r]
    let δk := fibredCategoryHomMk B S hS (c'.π.app k) hk
    let dx := fibredCategoryHomMk B S hS (D'.map r) (s := F.map (D'.map r).op a) rfl
    let dy := fibredCategoryHomMk B S hS (D'.map r) (s := F.map (D'.map r).op b) rfl
    let ψ := fibredCategoryHomMk B S hS (𝟙 (D'.obj k))
      (s := F.map (D'.map r).op a) (t := F.map (D'.map r).op b) (by rw [op_id, F.map_id]; exact hr)
    have hδk : (fibredCategory B S hS F).val.p.IsHomLift (c'.π.app k) δk :=
      isHomLift_fibredCategoryHomMk B S hS (c'.π.app k) hk
    have hdx : (fibredCategory B S hS F).val.p.IsHomLift (D'.map r) dx :=
      isHomLift_fibredCategoryHomMk B S hS (D'.map r) (s := F.map (D'.map r).op a) rfl
    have hdy : (fibredCategory B S hS F).val.p.IsHomLift (D'.map r) dy :=
      isHomLift_fibredCategoryHomMk B S hS (D'.map r) (s := F.map (D'.map r).op b) rfl
    have hψk : (fibredCategory B S hS F).val.p.IsHomLift (𝟙 (D'.obj k)) ψ :=
      isHomLift_fibredCategoryHomMk B S hS _ _
    refine ⟨k, r, ⟨_, rfl⟩, ⟨_, rfl⟩, dx, dy, δk, ψ, hdx, hdy, hδk, hψk, ?_, ?_⟩
    · have h₁ : (fibredCategory B S hS F).val.p.IsHomLift (c'.π.app k ≫ D'.map r) (δk ≫ dx) :=
        @IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ (c'.π.app k) (D'.map r) δk dx hδk hdx
      rw [c'.w r] at h₁
      exact hom_eq_of_isHomLift_fibredCategory B S hS (c'.π.app i) _ _
    · have h₁ : (fibredCategory B S hS F).val.p.IsHomLift (c'.π.app k ≫ 𝟙 _ ≫ D'.map r)
          (δk ≫ ψ ≫ dy) :=
        @IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ (c'.π.app k) _ δk (ψ ≫ dy) hδk
          (@IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ (𝟙 (D'.obj k)) (D'.map r) ψ dy hψk hdy)
      rw [Category.id_comp, c'.w r] at h₁
      have h₂ : (fibredCategory B S hS F).val.p.IsHomLift (𝟙 c'.pt ≫ c'.π.app i) (φ ≫ ε) :=
        inferInstance
      rw [Category.id_comp] at h₂
      exact hom_eq_of_isHomLift_fibredCategory B S hS (c'.π.app i) _ _
  · intro x
    obtain ⟨⟨bx, ⟨s⟩⟩, hbx⟩ := x
    change bx = _ at hbx
    subst hbx
    obtain ⟨j, a, ha⟩ := Types.jointly_surjective_of_isColimit hcol s
    exact ⟨j.unop, ⟨_, rfl⟩,
      fibredCategoryHomMk B S hS (c'.π.app j.unop) (s := s) (t := a) ha.symm, inferInstance⟩

end LimitPreserving

end AlgebraicGeometry.Stack

end
