module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPoints

/-!
# Transition morphisms between base changes in a family with a module

Let `f : X ⟶ S` be a morphism of schemes and let `T' ⟶ T` be a morphism of schemes over `S`.
This file provides the morphism `X ×_S T' ⟶ X ×_S T` induced on base changes, exhibits it as a
fibre product of `X ×_S T` and `T'` over `T`, and identifies the pullback along it of a module
pulled back from `X` with the module pulled back from `X` to `X ×_S T'`.

## Main definitions

* `AlgebraicGeometry.FreeAtGenericPointsSituation.transitionHom` is the transition morphism of
  base changes.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.transitionModuleIso` compares the two
  readings of the base-changed module.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.isPullback_transitionHom`: the transition
  morphism is the base change of the given morphism of schemes over `S`.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.flat_transitionHom`: it is flat as soon as
  the given morphism is.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.geometricallyIrreducible_baseChangeMap`: every
  base change of a family with geometrically irreducible fibres again has geometrically
  irreducible fibres, so each of its fibres is irreducible and has a generic point
  (`exists_isGenericPoint_fiber_baseChangeMap`).
* `AlgebraicGeometry.FreeAtGenericPointsSituation.mem_of_isGenericPoint`: an open set meeting a
  set with a generic point contains that generic point.

## Implementation notes

The constructions repeat, in public form, the fibre-product description of a transition of base
changes used in the proof that the fibrewise generic-point condition is stable under base
change. The limit cone is built by hand rather than by `pullback.map`, so that both of its legs
are the structural projections and no further comparison is needed when flatness is transported
along it.

## References

* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u})

/-- The transition morphism `X ×_S T' ⟶ X ×_S T` induced by a morphism `g : T' ⟶ T` of schemes
over `S`. -/
noncomputable def transitionHom {T T' : Over D.S} (g : T' ⟶ T) :
    pullback D.f T'.hom ⟶ pullback D.f T.hom :=
  pullback.lift (pullback.fst D.f T'.hom) (pullback.snd D.f T'.hom ≫ g.left) (by
    rw [Category.assoc, g.w]
    exact pullback.condition)

/-- The transition morphism is compatible with the projections to the total space. -/
@[simp]
lemma transitionHom_comp_fst {T T' : Over D.S} (g : T' ⟶ T) :
    D.transitionHom g ≫ pullback.fst D.f T.hom = pullback.fst D.f T'.hom :=
  pullback.lift_fst _ _ _

/-- The transition morphism is compatible with the projections to the base. -/
@[simp]
lemma transitionHom_comp_snd {T T' : Over D.S} (g : T' ⟶ T) :
    D.transitionHom g ≫ pullback.snd D.f T.hom = pullback.snd D.f T'.hom ≫ g.left :=
  pullback.lift_snd _ _ _

/-- The transition morphism of base changes exhibits `X ×_S T'` as a fibre product of `X ×_S T`
and `T'` over `T`. -/
theorem isPullback_transitionHom {T T' : Over D.S} (g : T' ⟶ T) :
    IsPullback (D.transitionHom g) (pullback.snd D.f T'.hom)
      (pullback.snd D.f T.hom) g.left :=
  IsPullback.of_right (by simpa using IsPullback.of_hasPullback D.f T'.hom)
    (transitionHom_comp_snd D g) (IsPullback.of_hasPullback D.f T.hom)

/-- The transition morphism is flat as soon as the morphism of schemes over `S` inducing it
is: it is a base change of that morphism. -/
theorem flat_transitionHom {T T' : Over D.S} (g : T' ⟶ T) [Flat g.left] :
    Flat (D.transitionHom g) :=
  MorphismProperty.of_isPullback (D.isPullback_transitionHom g).flip ‹_›

/-- The pullback along the transition morphism of the module on `X ×_S T` is the module on
`X ×_S T'`: both are pullbacks of the module on `X` along projections that agree. -/
noncomputable def transitionModuleIso {T T' : Over D.S} (g : T' ⟶ T) :
    (Scheme.Modules.pullback (D.transitionHom g)).obj (D.baseChangeModule T) ≅
      D.baseChangeModule T' :=
  (Scheme.Modules.pullbackComp (D.transitionHom g) (pullback.fst D.f T.hom)).app D.F ≪≫
    eqToIso (congrArg (fun k : pullback D.f T'.hom ⟶ D.X =>
      (Scheme.Modules.pullback k).obj D.F) (D.transitionHom_comp_fst g))

/-! ### Irreducibility of the fibres of a base change -/

/-- The family of the situation is geometrically irreducible: being so is exactly geometric
irreducibility of all its fibres. -/
theorem geometricallyIrreducible_f : GeometricallyIrreducible D.f :=
  (GeometricallyIrreducible.iff_geometricallyIrreducible_fiber D.f).mpr
    D.geometricallyIrreducibleFibers

/-- Every base change of the family is geometrically irreducible. -/
theorem geometricallyIrreducible_baseChangeMap (T : Over D.S) :
    GeometricallyIrreducible (D.baseChangeMap T) :=
  have := D.geometricallyIrreducible_f
  inferInstance

/-- Every fibre of a base change of the family is an irreducible space; in particular it is
nonempty. -/
theorem irreducibleSpace_fiber_baseChangeMap (T : Over D.S) (t : T.left) :
    IrreducibleSpace ((D.baseChangeMap T).fiber t) :=
  have := D.geometricallyIrreducible_f
  inferInstance

/-- Every fibre of a base change of the family has a generic point: it is irreducible, and the
underlying space of a scheme is sober. -/
theorem exists_isGenericPoint_fiber_baseChangeMap (T : Over D.S) (t : T.left) :
    ∃ ξ : (D.baseChangeMap T).fiber t, IsGenericPoint ξ (Set.univ : Set _) :=
  have := D.irreducibleSpace_fiber_baseChangeMap T t
  ⟨genericPoint _, genericPoint_spec _⟩

/-- An open subset of a space that contains some point of a set with a generic point contains
that generic point: the complement of the open set is closed, so it would otherwise contain the
whole closure of the generic point. -/
theorem mem_of_isGenericPoint {A : Type*} [TopologicalSpace A] {Z : Set A} {ξ : A}
    (hξ : IsGenericPoint ξ Z) {V : Set A} (hV : IsOpen V) {y : A} (hy : y ∈ V) (hyZ : y ∈ Z) :
    ξ ∈ V := by
  by_contra hmem
  have hsub : closure {ξ} ⊆ Vᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hmem) hV.isClosed_compl
  exact (hξ ▸ hsub) hyZ hy

/-- A surjective continuous map carries a generic point of the whole space to a generic point
of the whole space. -/
theorem isGenericPoint_univ_of_surjective {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (k : A → B) (hk : Continuous k) (hsurj : Function.Surjective k)
    {ξ : A} (hξ : IsGenericPoint ξ (Set.univ : Set A)) :
    IsGenericPoint (k ξ) (Set.univ : Set B) := by
  refine Set.eq_univ_iff_forall.mpr fun b ↦ ?_
  obtain ⟨a, rfl⟩ := hsurj b
  have ha : a ∈ closure ({ξ} : Set A) := hξ ▸ Set.mem_univ a
  simpa using image_closure_subset_closure_image hk ⟨a, ha, rfl⟩

/-- The comparison morphism of fibres induced by the transition morphism of base changes. -/
noncomputable def fiberTransitionHom {T T' : Over D.S} (g : T' ⟶ T) (t' : T'.left) :
    (D.baseChangeMap T').fiber t' ⟶ (D.baseChangeMap T).fiber (g.left t') :=
  pullback.map _ _ _ _ (D.transitionHom g)
    (Spec.map (Scheme.Hom.residueFieldMap g.left t')) g.left
    (D.isPullback_transitionHom g).w.symm
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g.left t').symm

/-- The comparison morphism of fibres is surjective: it is a base change of the surjection of
spectra of residue fields. -/
theorem surjective_fiberTransitionHom {T T' : Over D.S} (g : T' ⟶ T) (t' : T'.left) :
    Surjective (D.fiberTransitionHom g t') := by
  have hρ : Surjective (Spec.map (Scheme.Hom.residueFieldMap g.left t')) := by
    rw [surjective_iff]
    intro z
    have : Unique (PrimeSpectrum (T'.left.residueField t')) := PrimeSpectrum.instUnique
    have : Unique (PrimeSpectrum (T.left.residueField (g.left t'))) := PrimeSpectrum.instUnique
    exact ⟨default, Subsingleton.elim _ _⟩
  exact MorphismProperty.of_isPullback
    (isPullback_fiberToSpecResidueField_of_isPullback
      (D.isPullback_transitionHom g) t').flip hρ

/-- The comparison morphism of fibres is compatible with the inclusions of the fibres into the
base changes. -/
theorem transitionHom_fiberι {T T' : Over D.S} (g : T' ⟶ T) (t' : T'.left)
    (ξ' : (D.baseChangeMap T').fiber t') :
    D.transitionHom g ((D.baseChangeMap T').fiberι t' ξ') =
      (D.baseChangeMap T).fiberι (g.left t') (D.fiberTransitionHom g t' ξ') := by
  have hc : D.fiberTransitionHom g t' ≫ (D.baseChangeMap T).fiberι (g.left t') =
      (D.baseChangeMap T').fiberι t' ≫ D.transitionHom g := by
    dsimp [fiberTransitionHom, Scheme.Hom.fiberι, Scheme.Hom.fiber, pullback.map]
    simp only [pullback.lift_fst]
  simpa using
    (congrArg (fun k : (D.baseChangeMap T').fiber t' ⟶ pullback D.f T.hom => k ξ') hc).symm

/-- **The generic point of a fibre upstairs lies over the generic point of the fibre
downstairs.** The comparison morphism of fibres is surjective, so it carries a generic point to
a generic point, and a fibre of a base change of the family has exactly one of those. -/
theorem transitionHom_fiberι_of_isGenericPoint {T T' : Over D.S} (g : T' ⟶ T) (t' : T'.left)
    {ξ' : (D.baseChangeMap T').fiber t'} (hξ' : IsGenericPoint ξ' (Set.univ : Set _))
    {ξ : (D.baseChangeMap T).fiber (g.left t')} (hξ : IsGenericPoint ξ (Set.univ : Set _)) :
    D.transitionHom g ((D.baseChangeMap T').fiberι t' ξ') =
      (D.baseChangeMap T).fiberι (g.left t') ξ := by
  have himg : IsGenericPoint (D.fiberTransitionHom g t' ξ') (Set.univ : Set _) :=
    isGenericPoint_univ_of_surjective _ (D.fiberTransitionHom g t').continuous
      (D.surjective_fiberTransitionHom g t').surj hξ'
  rw [D.transitionHom_fiberι g t' ξ', himg.eq hξ]

end AlgebraicGeometry.FreeAtGenericPointsSituation

end
