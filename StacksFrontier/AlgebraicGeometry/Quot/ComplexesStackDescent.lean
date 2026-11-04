module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackBaseChange
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.IsStackFromRepresentableDiagonal

/-!
# Stacks 0DLH: `Complexes_{X/B}` is a stack in groupoids, given its inputs as hypotheses

Stacks 0DLH: in the situation of Stacks 0DLE, `p : Complexes_{X/B} ⟶ (Sch/S)_fppf` is a stack in
groupoids. The source's proof: the `Isom` presheaves are sheaves by Stacks 0DLG and 045G; given a
descent datum `(T_i, K_i, φ_ij)` relative to an fppf covering `{T_i ⟶ T}`, the morphisms
`T_i ⟶ B` glue to `T ⟶ B` because `B` is an fppf sheaf (Stacks 04P2), the complexes `K_i` glue to a
complex `E` on `X_T` with quasi-coherent cohomology by Stacks 0DLA (they have no negative
self-extensions by Stacks 0DLD(b)), and `E` is an object of `Complexes_{X/B}` over `T` because
`T`-perfectness descends (Stacks 0DL1 with 0DL2) and so does the condition on the fibres
(Stacks 0DLC(1)).

This file proves all of that except four results, which are hypotheses stated at their Stacks
content: `AlgebraicGeometry.Space.ComplexesSituation.CechDescent` (0DLA, Čech case),
`AlgebraicGeometry.Space.ComplexesSituation.HasNoNegativeSelfExt` (0DLD(b)),
`AlgebraicGeometry.Space.ComplexesSituation.RelativelyPerfectDescends` (0DL1 with 0DL2) and
`AlgebraicGeometry.Space.ComplexesSituation.NoNegativeFibreExtDescends` (0DLC(1)), plus Stacks 0DLG
in the form of the 0DLN skeleton.

## Main results

* `AlgebraicGeometry.Space.exists_comp_eq_of_compatible`: Stacks 04P2 for an algebraic space.
* `AlgebraicGeometry.Space.ComplexesSituation.CechCover.exists_glued`: the complexes of a Čech
  covering in `Complexes_{X/B}` glue to an object of `Complexes_{X/B}`.
* `AlgebraicGeometry.Space.ComplexesSituation.descentDatum_isEffective`: every descent datum of
  `Complexes_{X/B}` relative to an fppf covering is effective.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesFunctor_isStackInGroupoids_of_pending`:
  Stacks 0DLH, in the shape of the hypothesis `h0DLH` of the 0DLN skeleton
  (`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackAlgebraicityPending.lean`).

## Implementation notes

Terms of the derived categories here are hostile to the kernel: comparing `τ.hom.app M` with
`τ.hom.app M'` for `M`, `M'` that agree only up to unfolding makes it unfold the comparison
isomorphism `τ` itself, and statements elaborated inside a `def` carry their nested proofs as
auxiliary constants, so they agree with the same statements elaborated in a `theorem` only after
such unfolding. Two devices keep every comparison syntactic: the Čech data of 0DLA are bundled in
the structure `AlgebraicGeometry.Space.ComplexesSituation.CechCover`, of objects and morphisms of
`Complexes_{X/B}`, so that the descent datum supplies them as they are; and the compatibility of
the glued complex with the gluing isomorphisms is the structure
`AlgebraicGeometry.Space.ComplexesSituation.FibresCompatible`, whose field keeps the spelling it
is consumed with.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

section Generic

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]

/-- The comparison of two fibres `Lw.map uf ≫ wf` and `Lw.map vf ≫ wf` of composites with a common
outer factor `wf`, through the comparisons `τ`, `τ'` of the composite functors, is the conjugate
of `uf ≫ inv vf`. -/
theorem fibreComp_comp_inv_fibreComp {Lw : C₁ ⥤ C₀} {La : C₂ ⥤ C₁} {Lb : C₃ ⥤ C₁}
    {Lwa : C₂ ⥤ C₀} {Lwb : C₃ ⥤ C₀} (τ : Lwa ≅ La ⋙ Lw) (τ' : Lwb ≅ Lb ⋙ Lw) {M₀ : C₀}
    {M₁ : C₁} {M₂ : C₂} {M₃ : C₃} (wf : Lw.obj M₁ ⟶ M₀) [IsIso wf] (uf : La.obj M₂ ⟶ M₁)
    (vf : Lb.obj M₃ ⟶ M₁) [IsIso vf] :
    Functor.fibreComp τ wf uf ≫ inv (Functor.fibreComp τ' wf vf) =
      τ.hom.app M₂ ≫ Lw.map (uf ≫ inv vf) ≫ τ'.inv.app M₃ := by
  rw [IsIso.comp_inv_eq]
  simp only [Functor.fibreComp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- An `IsPullback` square stays one after conjugating its sides by `eqToHom`s. -/
theorem isPullback_eqToHom_conj {P P' X X' Y Y' Z : C₀} (hP : P' = P) (hX : X' = X)
    (hY : Y' = Y) {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) :
    IsPullback (eqToHom hP ≫ fst ≫ eqToHom hX.symm) (eqToHom hP ≫ snd ≫ eqToHom hY.symm)
      (eqToHom hX ≫ f) (eqToHom hY ≫ g) := by
  subst hP hX hY
  simpa using h

/-- An `IsPullback` square stays one after conjugating its sides by `eqToHom`s, the corner too. -/
theorem isPullback_eqToHom_conj' {P P' X X' Y Y' Z Z' : C₀} (hP : P' = P) (hX : X' = X)
    (hY : Y' = Y) (hZ : Z' = Z) {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) :
    IsPullback (eqToHom hP ≫ fst ≫ eqToHom hX.symm) (eqToHom hP ≫ snd ≫ eqToHom hY.symm)
      (eqToHom hX ≫ f ≫ eqToHom hZ.symm) (eqToHom hY ≫ g ≫ eqToHom hZ.symm) := by
  subst hP hX hY hZ
  simpa using h

/-- Two fibres `Functor.fibreComp τ nf ψ₁` and `Functor.fibreComp τ' mf ψ₂` of composites out of
one object agree through `x` as soon as `ψ₁` and `ψ₂` agree through the comparison
`nf ≫ inv mf`. -/
theorem comp_fibreComp_eq_fibreComp {C₁' : Type*} [Category* C₁'] {Lp : C₁ ⥤ C₀}
    {La : C₂ ⥤ C₁} {Lpa : C₂ ⥤ C₀} {Lq : C₁' ⥤ C₀} {La' : C₂ ⥤ C₁'} {Lqa : C₂ ⥤ C₀}
    (τ : Lpa ≅ La ⋙ Lp) (τ' : Lqa ≅ La' ⋙ Lq) {M : C₂} {K₁ : C₁} {K₂ : C₁'} {Q : C₀}
    (ψ₁ : La.obj M ⟶ K₁) (ψ₂ : La'.obj M ⟶ K₂) (nf : Lp.obj K₁ ⟶ Q) (mf : Lq.obj K₂ ⟶ Q)
    [IsIso mf] (x : Lpa.obj M ⟶ Lqa.obj M)
    (h : τ.hom.app M ≫ Lp.map ψ₁ ≫ (nf ≫ inv mf) = x ≫ τ'.hom.app M ≫ Lq.map ψ₂) :
    x ≫ Functor.fibreComp τ' mf ψ₂ = Functor.fibreComp τ nf ψ₁ := by
  simp only [Functor.fibreComp]
  have h' := congrArg (· ≫ mf) h
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] at h'
  exact h'.symm

/-- In a triple fibre product, an endomorphism fixing the first double projection, whose
composite with an endomorphism fixing the second double projection fixes the third, is the
identity. -/
theorem eq_id_of_tripleOverlap {Vi Vj Vk U Vij Vjk Vik W : C₀} {fi : Vi ⟶ U} {fj : Vj ⟶ U}
    {fk : Vk ⟶ U} {pij₁ : Vij ⟶ Vi} {pij₂ : Vij ⟶ Vj} {pjk₁ : Vjk ⟶ Vj} {pjk₂ : Vjk ⟶ Vk}
    {pik₁ : Vik ⟶ Vi} {pik₂ : Vik ⟶ Vk} (_hij : IsPullback pij₁ pij₂ fi fj)
    (hjk : IsPullback pjk₁ pjk₂ fj fk) {s₁₂ : W ⟶ Vij} {s₂₃ : W ⟶ Vjk} {s₁₃ : W ⟶ Vik}
    (hW : IsPullback s₁₂ s₂₃ pij₂ pjk₁) (_h₁ : s₁₃ ≫ pik₁ = s₁₂ ≫ pij₁)
    (h₃ : s₁₃ ≫ pik₂ = s₂₃ ≫ pjk₂) {γ γ' γ'' : W ⟶ W} (hγ : γ ≫ s₁₂ = s₁₂)
    (hγ' : γ' ≫ s₂₃ = s₂₃) (hγ'' : γ'' ≫ s₁₃ = s₁₃) (hc : γ'' = γ ≫ γ') : γ = 𝟙 W := by
  have e₃ : γ ≫ s₂₃ ≫ pjk₂ = s₂₃ ≫ pjk₂ := by
    have := congrArg (· ≫ pik₂) hγ''
    simp only [Category.assoc, hc] at this
    rw [h₃, ← Category.assoc γ' s₂₃, hγ'] at this
    exact this
  have e₂ : γ ≫ s₂₃ = s₂₃ := by
    refine hjk.hom_ext ?_ ?_
    · rw [Category.assoc, ← hW.w, ← Category.assoc, hγ, hW.w]
    · rw [Category.assoc, e₃]
  exact hW.hom_ext (by rw [hγ, Category.id_comp]) (by rw [e₂, Category.id_comp])

open Functor in
/-- **A descent datum is effective as soon as its objects map compatibly to one object.** In a
category fibred over `𝒞`, let `𝔇` be a descent datum relative to a covering `{f i : V i ⟶ U}`,
and let `ζ i : 𝔇.x i ⟶ x` be strongly cartesian morphisms over `f i` into an object `x` over `U`
whose two restrictions to every double overlap agree through the gluing isomorphism `𝔇.φ i j`.
Then `x`, read as glued from the `𝔇.x i` through the `ζ i`, makes `𝔇` effective. -/
theorem descentDatum_isEffective_of_compatible {𝒞 : Type*} {𝒮 : Type*} [Category* 𝒞]
    [Category* 𝒮] {p : 𝒮 ⥤ 𝒞} {U : 𝒞} {I : Type*} {V : I → 𝒞} {f : ∀ i, V i ⟶ U}
    {Vij : I → I → 𝒞} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
    {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)} {Vijk : I → I → I → 𝒞}
    {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
    {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
    {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
    {q₃ : ∀ i j k, Vijk i j k ⟶ V k} {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
    {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
    {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
    (𝔇 : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (x : 𝒮) (hx : p.obj x = U) (ζ : ∀ i, 𝔇.x i ⟶ x)
    (hζ : ∀ i, p.IsStronglyCartesian (f i) (ζ i))
    (hc : ∀ i j, (𝔇.xrij i j).hom ≫ ζ i = (𝔇.φ i j ≫ (𝔇.xrji i j).hom) ≫ ζ j) :
    𝔇.IsEffective := by
  refine ⟨x, hx, fun i => Restriction.ofCartesian (𝔇.hx i) hx _ (hζ i), fun i => 𝟙 (𝔇.x i),
    fun i => FibreHom.id p _ (𝔇.hx i), fun i => IsIso.id (𝔇.x i), fun i j => ?_⟩
  have hid : ∀ {W V' : 𝒞} {g : W ⟶ V'} {y : 𝒮} (hy : p.obj y = V') (r : Restriction p g y hy),
      r.hom = Restriction.compTo p g (𝟙 V') (by simp) (Restriction.id p y hy) r :=
    fun {_ _ g _} hy r => Restriction.eq_compTo g (𝟙 _) (by simp) (Restriction.id p _ hy) r
      r.hom r.isHomLift_hom (Category.comp_id _)
  have hcart : p.IsStronglyCartesian (pr₁ i j ≫ f i) ((𝔇.xrij i j).hom ≫ ζ i) := by
    have h1 := (𝔇.xrij i j).isStronglyCartesian_hom
    have h2 := hζ i
    exact inferInstance
  refine ⟨Restriction.ofCartesian (𝔇.xrij i j).hpt hx _ hcart, 𝟙 (𝔇.xrij i j).pt, 𝔇.φ i j,
    FibreHom.id p _ (𝔇.xrij i j).hpt, 𝔇.φ_fibreHom i j, IsIso.id (𝔇.xrij i j).pt,
    𝔇.φ_iso i j, ?_, ?_, Category.id_comp _⟩
  · unfold IsRestrictionOf
    rw [← hid (𝔇.hx i) (𝔇.xrij i j),
      ← Restriction.eq_compTo (pr₁ i j) (f i) rfl _ _ (𝔇.xrij i j).hom
        (𝔇.xrij i j).isHomLift_hom rfl]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have hφlift : p.IsHomLift (pr₂ i j) (𝔇.φ i j ≫ (𝔇.xrji i j).hom) := by
      have h1 : p.IsHomLift (𝟙 (Vij i j)) (𝔇.φ i j) := (fibreHomMk (𝔇.φ_fibreHom i j)).2
      have h2 : p.IsHomLift (pr₂ i j) ((𝔇.xrji i j).hom) := (𝔇.xrji i j).isHomLift_hom
      exact isHomLift_of_eq (n := 𝟙 (Vij i j) ≫ pr₂ i j) inferInstance (by simp)
    unfold IsRestrictionOf
    rw [← hid (𝔇.hx j) (𝔇.xrji i j),
      ← Restriction.eq_compTo (pr₂ i j) (f j) (hVij i j).w _ _ (𝔇.φ i j ≫ (𝔇.xrji i j).hom)
        hφlift (hc i j).symm]
    exact (Category.comp_id _).symm

end Generic

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 04P2 for an algebraic space.** Morphisms `y i : W i ⟶ Y` from the members of an fppf
covering `{b i : W i ⟶ U}` into an algebraic space `Y`, which agree on every `Z` mapping to two
members compatibly over `U`, glue to a morphism `U ⟶ Y`: an algebraic space is an fppf sheaf. -/
theorem exists_comp_eq_of_compatible (Y : AlgebraicSpaces B S hS) {U : BigFppfOver B S hS}
    {I : Type*} (W : I → BigFppfOver B S hS) (b : ∀ i, W i ⟶ U)
    (hcov : Sieve.ofArrows W b ∈ BigFppfOver.topology B S hS U)
    (y : ∀ i, (schemeSpaceFunctor B S hS).obj (W i) ⟶ Y)
    (hy : ∀ i j (Z : BigFppfOver B S hS) (gi : Z ⟶ W i) (gj : Z ⟶ W j), gi ≫ b i = gj ≫ b j →
      (schemeSpaceFunctor B S hS).map gi ≫ y i = (schemeSpaceFunctor B S hS).map gj ≫ y j) :
    ∃ g : (schemeSpaceFunctor B S hS).obj U ⟶ Y,
      ∀ i, (schemeSpaceFunctor B S hS).map (b i) ≫ g = y i := by
  have hsh : (Presieve.ofArrows W b).IsSheafFor Y.1 :=
    (Presieve.isSheafFor_iff_generate _).mpr
      (((isSheaf_iff_isSheaf_of_type _ _).mp Y.2.isSheaf) _ hcov)
  let y' : ∀ i, yoneda.obj (W i) ⟶ Y.1 := fun i => (y i).hom
  have hcompat : Presieve.Arrows.Compatible Y.1 b (fun i => yonedaEquiv (y' i)) := by
    intro i j Z gi gj h
    simp only [map_yonedaEquiv]
    have := congrArg
      (fun φ : (schemeSpaceFunctor B S hS).obj Z ⟶ Y => φ.hom.app (Opposite.op Z) (𝟙 Z))
      (hy i j Z gi gj h)
    simp only at this
    exact this
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hsh _ hcompat
  refine ⟨ObjectProperty.homMk (yonedaEquiv.symm t), fun i => ?_⟩
  apply ObjectProperty.hom_ext
  change yoneda.map (b i) ≫ yonedaEquiv.symm t = y' i
  rw [yonedaEquiv_symm_naturality_left, ht i, Equiv.symm_apply_apply]

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

attribute [local instance 2000] inverseImageRingedSite_hasWeakSheafify_over
  inverseImageRingedSite_wEqualsLocallyBijective_over

attribute [local instance] inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  inverseImageRingedSite_slice_hasDerivedCategory RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  inverseImageRingedSite_slice_sheafTensor_additive
  inverseImageRingedSite_slice_sheafTensor_obj_additive
  inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  instModulesHasDerivedCategory

/-- A complex on `X_T` has quasi-coherent cohomology sheaves: it lies in `D_QCoh(O_{X_T})`. -/
def HasQuasicoherentCohomology (T : SchemesOver D.Y) (E : derivedModules B S hS (D.space T)) :
    Prop :=
  ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    n).obj E).IsQuasicoherentOnSite

/-- **Stacks 0DLD(b) at `V = T`.** Every object `(T, E)` of `Complexes_{X/B}` has no negative
self-extensions: `Ext^n(E, E) = 0` for `n < 0`. -/
def HasNoNegativeSelfExt : Prop :=
  ∀ (A : ComplexesObject D) (n : ℤ), n < 0 → Subsingleton (A.E ⟶ A.E⟦n⟧)

/-- The restriction along `s : Z ⟶ T'` of a morphism `φ : L a^* M₁ ⟶ L b^* M₂` between pullbacks
along two maps out of `T'`, read between the pullbacks along `s ≫ a` and `s ≫ b`. -/
abbrev restrictComparison {T₁ T₂ T' Z : SchemesOver D.Y} {a : T' ⟶ T₁} {b : T' ⟶ T₂}
    {M₁ : derivedModules B S hS (D.space T₁)} {M₂ : derivedModules B S hS (D.space T₂)}
    (φ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).obj M₁ ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj M₂) (s : Z ⟶ T') :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (s ≫ a))).obj M₁ ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (s ≫ b))).obj M₂ :=
  (D.compComparison s a).hom.app M₁ ≫
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap s)).map φ ≫
    (D.compComparison s b).inv.app M₂

/-- **Stacks 0DL1 with Stacks 0DL2.** Relative perfectness descends along an fppf covering: a
complex on `X_T` with quasi-coherent cohomology whose pullbacks to the members `T_i` of an fppf
covering of `T` are `T_i`-perfect is `T`-perfect. It holds:
`AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectDescends`, in
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackPerfectDescent.lean`. -/
def RelativelyPerfectDescends : Prop :=
  ∀ (T : SchemesOver D.Y) {I : Type (u + 1)} (Ti : I → SchemesOver D.Y) (a : ∀ i, Ti i ⟶ T),
    Sieve.ofArrows (fun i => (Ti i).left) (fun i => (a i).left) ∈
      BigFppfOver.topology B S hS T.left →
    ∀ E : derivedModules B S hS (D.space T), D.HasQuasicoherentCohomology T E →
      (∀ i, D.IsRelativelyPerfect (Ti i)
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (a i))).obj E)) →
      D.IsRelativelyPerfect T E

/-- **Stacks 0DLC(1).** The condition on the fibres of `Complexes_{X/B}` descends along an fppf
covering: a `T`-perfect complex on `X_T` whose pullbacks to the members `T_i` of an fppf covering
of `T` satisfy it satisfies it. -/
def NoNegativeFibreExtDescends : Prop :=
  ∀ (T : SchemesOver D.Y) {I : Type (u + 1)} (Ti : I → SchemesOver D.Y) (a : ∀ i, Ti i ⟶ T),
    Sieve.ofArrows (fun i => (Ti i).left) (fun i => (a i).left) ∈
      BigFppfOver.topology B S hS T.left →
    ∀ E : derivedModules B S hS (D.space T), D.IsRelativelyPerfect T E →
      (∀ i, D.HasNoNegativeFibreExt (Ti i)
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (a i))).obj E)) →
      D.HasNoNegativeFibreExt T E

variable {D}

/-- The condition on the fibres of `Complexes_{X/B}` is invariant under isomorphism. -/
theorem hasNoNegativeFibreExt_of_iso {T : SchemesOver D.Y}
    {E E' : derivedModules B S hS (D.space T)}
    (e : E ≅ E') (hE' : D.HasNoNegativeFibreExt T E') : D.HasNoNegativeFibreExt T E := by
  intro T₀ hT₀ y i hi
  have e' := ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).mapIso e
  have := hE' T₀ hT₀ y i hi
  exact Equiv.subsingleton (e'.homCongr ((shiftFunctor _ i).mapIso e'))

/-- Relative perfectness is invariant under isomorphism. -/
theorem isRelativelyPerfect_of_iso {T : SchemesOver D.Y} {E E' : derivedModules B S hS (D.space T)}
    (e : E ≅ E') (hE' : D.IsRelativelyPerfect T E') : D.IsRelativelyPerfect T E :=
  let : ∀ U : (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).C,
      HasDerivedCategory (SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).O).over U)) :=
    fun _ => HasDerivedCategory.standard _
  (isClosedUnderIsomorphisms_isPerfectRelativeToCanonical B S hS (D.projection T)
    (D.projection_isFlat T) (D.projection_isLocallyOfFinitePresentation T)).of_iso e.symm hE'

attribute [local instance] complexesCategory

/-- The comparison `L u^* A.E ⟶ L v^* A'.E` of the fibres of two morphisms `u : Q ⟶ A` and
`v : Q ⟶ A'` of `Complexes_{X/B}` out of one object: for the two projections of a double overlap
it is the gluing isomorphism of a descent datum. -/
abbrev homComparison {Q A A' : ComplexesObject D} (u : ComplexesHom Q A) (v : ComplexesHom Q A') :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap u.base)).obj A.E ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap v.base)).obj A'.E :=
  u.fibre ≫ inv v.fibre

/-- The inverse of the comparison of the pullbacks along two equal maps is an `eqToHom`. -/
theorem relativeMapComparison_inv_app' {T T' : SchemesOver D.Y} {h h' : T ⟶ T'} (e : h = h')
    (M : derivedModules B S hS (D.space T')) :
    (D.relativeMapComparison e).inv.app M =
      eqToHom (congrArg
        (fun k : T ⟶ T' =>
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj M) e.symm) := by
  subst e
  rfl



/-- Two equal morphisms of `Complexes_{X/B}` given by their bases and fibres have fibres agreeing
through the comparison of the two pullback functors. -/
theorem relativeMapComparison_comp_fibre_of_mk_eq {Q A : ComplexesObject D} {b b' : Q.T ⟶ A.T}
    {f : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj A.E ⟶ Q.E}
    {f' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b')).obj A.E ⟶ Q.E}
    {i : IsIso f} {i' : IsIso f'}
    (e : (⟨b, f, i⟩ : ComplexesHom Q A) = ⟨b', f', i'⟩) (hb : b = b') :
    (D.relativeMapComparison hb).hom.app A.E ≫ f' = f := by
  cases e
  rw [D.relativeMapComparison_hom_app, eqToHom_refl, Category.id_comp]

/-- The fibres of two equal composites of morphisms of `Complexes_{X/B}` agree through the
comparison of the two pullback functors. -/
theorem relativeMapComparison_comp_fibreComp_of_eq {Q X X' A : ComplexesObject D}
    (w : ComplexesHom Q X) (v : ComplexesHom X A) (w' : ComplexesHom Q X')
    (v' : ComplexesHom X' A) (e : w.comp v = w'.comp v')
    (hb : w.base ≫ v.base = w'.base ≫ v'.base) :
    (D.relativeMapComparison hb).hom.app A.E ≫
        Functor.fibreComp (D.compComparison w'.base v'.base) w'.fibre v'.fibre =
      Functor.fibreComp (D.compComparison w.base v.base) w.fibre v.fibre :=
  relativeMapComparison_comp_fibre_of_mk_eq e hb

/-- The cocycle identity for comparisons `F₁ ≫ inv F₂` of fibres, with the bases moved along
equalities `b₁`, `b₂`, `b₃`. -/
theorem fibre_cocycle {Q A₁ A₂ A₃ : ComplexesObject D} {β₁ β₁' : Q.T ⟶ A₁.T}
    {β₂ β₂' : Q.T ⟶ A₂.T} {β₃ β₃' : Q.T ⟶ A₃.T}
    (F₁ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap β₁)).obj A₁.E ⟶ Q.E)
    (F₁' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap β₁')).obj A₁.E ⟶ Q.E)
    (F₂ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap β₂)).obj A₂.E ⟶ Q.E)
    (F₂' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap β₂')).obj A₂.E ⟶ Q.E)
    (F₃ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap β₃)).obj A₃.E ⟶ Q.E)
    (F₃' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap β₃')).obj A₃.E ⟶ Q.E)
    [IsIso F₂] [IsIso F₃] [IsIso F₃'] (b₁ : β₁ = β₁') (b₂ : β₂ = β₂') (b₃ : β₃ = β₃')
    (e₁ : (D.relativeMapComparison b₁).hom.app A₁.E ≫ F₁' = F₁)
    (e₂ : (D.relativeMapComparison b₂).hom.app A₂.E ≫ F₂' = F₂)
    (e₃ : (D.relativeMapComparison b₃).hom.app A₃.E ≫ F₃' = F₃) :
    (F₁ ≫ inv F₂) ≫ (D.relativeMapComparison b₂).hom.app A₂.E ≫ (F₂' ≫ inv F₃) =
      (D.relativeMapComparison b₁).hom.app A₁.E ≫ (F₁' ≫ inv F₃') ≫
        (D.relativeMapComparison b₃).inv.app A₃.E := by
  subst b₁ b₂ b₃
  rw [D.relativeMapComparison_hom_app, eqToHom_refl, Category.id_comp] at e₁ e₂ e₃
  subst e₁ e₂ e₃
  simp only [D.relativeMapComparison_hom_app, relativeMapComparison_inv_app', eqToHom_refl,
    Category.id_comp, Category.comp_id, Category.assoc, IsIso.inv_hom_id_assoc]

/-- **The cocycle identity of the comparisons on a triple overlap.** For morphisms out of a triple
overlap `Q` to three double overlaps, and morphisms from those to three objects, whose composites
to each object agree, the restrictions of the three comparisons `homComparison` satisfy the cocycle
identity. -/
theorem restrictComparison_cocycle {Q X₁₂ X₂₃ X₁₃ A₁ A₂ A₃ : ComplexesObject D}
    (c₁ : ComplexesHom Q X₁₂) (d : ComplexesHom Q X₂₃) (c₃ : ComplexesHom Q X₁₃)
    (n₁₂ : ComplexesHom X₁₂ A₁) (m₁₂ : ComplexesHom X₁₂ A₂) (n₂₃ : ComplexesHom X₂₃ A₂)
    (m₂₃ : ComplexesHom X₂₃ A₃) (n₁₃ : ComplexesHom X₁₃ A₁) (m₁₃ : ComplexesHom X₁₃ A₃)
    (e₁ : c₁.comp n₁₂ = c₃.comp n₁₃) (e₂ : c₁.comp m₁₂ = d.comp n₂₃)
    (e₃ : d.comp m₂₃ = c₃.comp m₁₃) (h₁ : c₁.base ≫ n₁₂.base = c₃.base ≫ n₁₃.base)
    (h₂ : c₁.base ≫ m₁₂.base = d.base ≫ n₂₃.base) (h₃ : d.base ≫ m₂₃.base = c₃.base ≫ m₁₃.base) :
    D.restrictComparison (homComparison n₁₂ m₁₂) c₁.base ≫
        (D.relativeMapComparison h₂).hom.app A₂.E ≫
        D.restrictComparison (homComparison n₂₃ m₂₃) d.base =
      (D.relativeMapComparison h₁).hom.app A₁.E ≫
        D.restrictComparison (homComparison n₁₃ m₁₃) c₃.base ≫
        (D.relativeMapComparison h₃).inv.app A₃.E := by
  rw [restrictComparison, restrictComparison, restrictComparison, homComparison, homComparison,
    homComparison]
  rw [← fibreComp_comp_inv_fibreComp (D.compComparison c₁.base n₁₂.base)
      (D.compComparison c₁.base m₁₂.base) c₁.fibre n₁₂.fibre m₁₂.fibre,
    ← fibreComp_comp_inv_fibreComp (D.compComparison d.base n₂₃.base)
      (D.compComparison d.base m₂₃.base) d.fibre n₂₃.fibre m₂₃.fibre,
    ← fibreComp_comp_inv_fibreComp (D.compComparison c₃.base n₁₃.base)
      (D.compComparison c₃.base m₁₃.base) c₃.fibre n₁₃.fibre m₁₃.fibre]
  exact fibre_cocycle _ _ _ _ _ _ h₁ h₂ h₃
    (relativeMapComparison_comp_fibreComp_of_eq c₁ n₁₂ c₃ n₁₃ e₁ h₁)
    (relativeMapComparison_comp_fibreComp_of_eq c₁ m₁₂ d n₂₃ e₂ h₂)
    (relativeMapComparison_comp_fibreComp_of_eq d m₂₃ c₃ m₁₃ e₃ h₃)

/-- **Compatibility of fibres with a gluing isomorphism.** For morphisms `n : Q ⟶ A` and
`m : Q ⟶ A'` of `Complexes_{X/Y}` and base maps `a : A.T ⟶ T`, `a' : A'.T ⟶ T` agreeing on `Q.T`,
the morphisms `ψ : L a^* E ⟶ A.E` and `ψ' : L a'^* E ⟶ A'.E` are compatible with the gluing
isomorphism `homComparison n m : L n^* A.E ⟶ L m^* A'.E`: the square
`L n^* ψ ≫ homComparison n m = L m^* ψ'` commutes, the canonical comparisons of the iterated
pullbacks of `E` inserted.

This is a structure rather than a definition so that its statement keeps the instance arguments
it is elaborated with, which the lemmas consuming it are elaborated with too. -/
structure FibresCompatible {Q A A' : ComplexesObject D} (n : ComplexesHom Q A)
    (m : ComplexesHom Q A')
    {T : SchemesOver D.Y} (E : derivedModules B S hS (D.space T)) {a : A.T ⟶ T} {a' : A'.T ⟶ T}
    (hb : n.base ≫ a = m.base ≫ a')
    (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).obj E ⟶ A.E)
    (ψ' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a')).obj E ⟶ A'.E) :
    Prop where
  /-- The compatibility square. -/
  eq : (D.compComparison n.base a).hom.app E ≫
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap n.base)).map ψ ≫
        homComparison n m =
    (D.relativeMapComparison hb).hom.app E ≫ (D.compComparison m.base a').hom.app E ≫
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map ψ'

/-- Two morphisms of `Complexes_{X/Y}` given by their bases and fibres agree as soon as their
bases agree and their fibres agree through the comparison of the two pullback functors. -/
theorem mk_eq_mk_of_relativeMapComparison {Q A : ComplexesObject D} {b b' : Q.T ⟶ A.T}
    (hb : b = b')
    {f : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj A.E ⟶ Q.E}
    {f' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b')).obj A.E ⟶ Q.E}
    (i : IsIso f) (i' : IsIso f') (h : (D.relativeMapComparison hb).hom.app A.E ≫ f' = f) :
    (⟨b, f, i⟩ : ComplexesHom Q A) = ⟨b', f', i'⟩ := by
  subst hb
  rw [D.relativeMapComparison_hom_app, eqToHom_refl, Category.id_comp] at h
  subst h
  rfl

/-- Two composites `n ≫ ⟨a, ψ⟩` and `m ≫ ⟨a', ψ'⟩` of morphisms of `Complexes_{X/Y}` out of one
object agree as soon as their bases agree and the fibres `ψ`, `ψ'` are compatible with the
comparison `homComparison n m` of the fibres of `n` and `m`. -/
theorem comp_mk_eq_comp_mk {Q A A' X : ComplexesObject D} (n : ComplexesHom Q A)
    (m : ComplexesHom Q A') {a : A.T ⟶ X.T} {a' : A'.T ⟶ X.T}
    (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).obj X.E ⟶ A.E)
    (ψ' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a')).obj X.E ⟶ A'.E)
    (hψ : IsIso ψ) (hψ' : IsIso ψ') (hb : n.base ≫ a = m.base ≫ a')
    (h : FibresCompatible n m X.E hb ψ ψ') :
    n.comp ⟨a, ψ, hψ⟩ = m.comp ⟨a', ψ', hψ'⟩ :=
  mk_eq_mk_of_relativeMapComparison hb _ _
    (comp_fibreComp_eq_fibreComp (D.compComparison n.base a) (D.compComparison m.base a') ψ ψ'
      n.fibre m.fibre _ h.eq)

/-- **The Čech data of an fppf covering in `Complexes_{X/Y}`.** An fppf covering
`{a i : T i ⟶ T}` in `(Sch/Y)_fppf` together with objects `X i` of `Complexes_{X/Y}` over the
`T i`, objects `X₂ i j` over genuine fibre products `T i ×_T T j` (`isPullback₂`) with morphisms
`n i j` and `m i j` to `X i` and `X j`, and objects `X₃ i j k` over genuine triple fibre products
`T i ×_T T j ×_T T k = (T i ×_T T j) ×_{T j} (T j ×_T T k)` (`isPullback₃`) with morphisms to the
three double overlaps, such that the two ways of mapping `X₃ i j k` to each `X i`, `X j`, `X k`
agree in `Complexes_{X/Y}` (`comp₁`, `comp₂`, `comp₃`).

This is the input of Stacks 0DLA in its Čech form: the complexes `K_i = (X i).E`, the gluing
isomorphisms `φ_ij = homComparison (n i j) (m i j) : L p₁^* K_i ≅ L p₂^* K_j` on the double
overlaps, and their cocycle condition on the triple overlaps, which is
`AlgebraicGeometry.Space.ComplexesSituation.CechCover.cocycle`. -/
structure CechCover (T : SchemesOver D.Y) (I : Type (u + 1)) where
  /-- The objects over the members of the covering. -/
  X : I → ComplexesObject D
  /-- The members of the covering. -/
  a : ∀ i, (X i).T ⟶ T
  /-- They form an fppf covering. -/
  covers : Sieve.ofArrows (fun i => (X i).T.left) (fun i => (a i).left) ∈
    BigFppfOver.topology B S hS T.left
  /-- The objects over the double overlaps. -/
  X₂ : I → I → ComplexesObject D
  /-- The morphisms from a double overlap to its first index. -/
  n : ∀ i j, ComplexesHom (X₂ i j) (X i)
  /-- The morphisms from a double overlap to its second index. -/
  m : ∀ i j, ComplexesHom (X₂ i j) (X j)
  /-- The double overlaps are fibre products. -/
  isPullback₂ : ∀ i j, IsPullback (n i j).base.left (m i j).base.left (a i).left (a j).left
  /-- The objects over the triple overlaps. -/
  X₃ : I → I → I → ComplexesObject D
  /-- The morphisms from a triple overlap to the overlap of its first two indices. -/
  c₁₂ : ∀ i j k, ComplexesHom (X₃ i j k) (X₂ i j)
  /-- The morphisms from a triple overlap to the overlap of its last two indices. -/
  c₂₃ : ∀ i j k, ComplexesHom (X₃ i j k) (X₂ j k)
  /-- The morphisms from a triple overlap to the overlap of its outer indices. -/
  c₁₃ : ∀ i j k, ComplexesHom (X₃ i j k) (X₂ i k)
  /-- The triple overlaps are fibre products of the double ones. -/
  isPullback₃ : ∀ i j k, IsPullback (c₁₂ i j k).base.left (c₂₃ i j k).base.left
    (m i j).base.left (n j k).base.left
  /-- The two morphisms from a triple overlap to its first index agree. -/
  comp₁ : ∀ i j k, (c₁₂ i j k).comp (n i j) = (c₁₃ i j k).comp (n i k)
  /-- The two morphisms from a triple overlap to its middle index agree. -/
  comp₂ : ∀ i j k, (c₁₂ i j k).comp (m i j) = (c₂₃ i j k).comp (n j k)
  /-- The two morphisms from a triple overlap to its last index agree. -/
  comp₃ : ∀ i j k, (c₂₃ i j k).comp (m j k) = (c₁₃ i j k).comp (m i k)

namespace CechCover

variable {T : SchemesOver D.Y} {I : Type (u + 1)} (C : CechCover T I)

/-- The two projections of a double overlap agree over `T`. -/
theorem w (i j : I) : (C.n i j).base ≫ C.a i = (C.m i j).base ≫ C.a j :=
  CostructuredArrow.hom_ext _ _
    (by simpa only [CostructuredArrow.comp_left] using (C.isPullback₂ i j).w)

/-- The base of `CechCover.comp₁`. -/
theorem w₁ (i j k : I) :
    (C.c₁₂ i j k).base ≫ (C.n i j).base = (C.c₁₃ i j k).base ≫ (C.n i k).base :=
  congrArg ComplexesHom.base (C.comp₁ i j k)

/-- The base of `CechCover.comp₂`. -/
theorem w₂ (i j k : I) :
    (C.c₁₂ i j k).base ≫ (C.m i j).base = (C.c₂₃ i j k).base ≫ (C.n j k).base :=
  congrArg ComplexesHom.base (C.comp₂ i j k)

/-- The base of `CechCover.comp₃`. -/
theorem w₃ (i j k : I) :
    (C.c₂₃ i j k).base ≫ (C.m j k).base = (C.c₁₃ i j k).base ≫ (C.m i k).base :=
  congrArg ComplexesHom.base (C.comp₃ i j k)

/-- **The cocycle condition of a Čech covering.** The gluing isomorphisms
`φ_ij = homComparison (n i j) (m i j)` of a Čech covering satisfy the cocycle condition of
Stacks 0DLA on the triple overlaps: `φ_jk ∘ φ_ij = φ_ik` after restriction, the canonical
comparisons of the iterated pullbacks inserted. -/
theorem cocycle (i j k : I) :
    D.restrictComparison (homComparison (C.n i j) (C.m i j)) (C.c₁₂ i j k).base ≫
        (D.relativeMapComparison (C.w₂ i j k)).hom.app (C.X j).E ≫
        D.restrictComparison (homComparison (C.n j k) (C.m j k)) (C.c₂₃ i j k).base =
      (D.relativeMapComparison (C.w₁ i j k)).hom.app (C.X i).E ≫
        D.restrictComparison (homComparison (C.n i k) (C.m i k)) (C.c₁₃ i j k).base ≫
        (D.relativeMapComparison (C.w₃ i j k)).inv.app (C.X k).E :=
  restrictComparison_cocycle _ _ _ _ _ _ _ _ _ (C.comp₁ i j k) (C.comp₂ i j k) (C.comp₃ i j k)
    _ _ _

end CechCover

variable (D) in
/-- **Stacks 0DLA, Čech case.** Descent of objects of the derived category along an fppf covering,
for objects without negative self-extensions: given a Čech covering `C` of `T` in `Complexes_{X/Y}`
whose complexes have no negative self-extensions after any base change, there is a complex `E` on
`X_T` with quasi-coherent cohomology and isomorphisms `ψ i : L a_i^* E ≅ K_i` compatible with the
gluing isomorphisms `homComparison (n i j) (m i j)` on the double overlaps.

Stacks 0DLA asks `K_i ∈ D_QCoh(O_{X_{T_i}})` with `Ext^p(K_i, K_i) = 0` for `p < 0`; here the
`K_i` are `T_i`-perfect (they are objects of `Complexes_{X/Y}`) and the vanishing is asked of
every base change, so the statement follows from 0DLA. The gluing data come as morphisms of
`Complexes_{X/Y}`, and their cocycle condition is `CechCover.cocycle`. -/
def CechDescent : Prop :=
  ∀ (T : SchemesOver D.Y) {I : Type (u + 1)} (C : CechCover T I),
    (∀ i (V : SchemesOver D.Y) (h : V ⟶ (C.X i).T) (n : ℤ), n < 0 →
      Subsingleton
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj (C.X i).E ⟶
          (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj (C.X i).E)⟦n⟧)) →
    ∃ (E : derivedModules B S hS (D.space T))
      (ψ : ∀ i, ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (C.a i))).obj E ≅
        (C.X i).E),
      D.HasQuasicoherentCohomology T E ∧
      ∀ i j, FibresCompatible (C.n i j) (C.m i j) E (C.w i j) (ψ i).hom (ψ j).hom

/-- Under Stacks 0DLD(b), every base change of the complex of an object of `Complexes_{X/Y}` has
no negative self-extensions. -/
theorem subsingleton_pull_shift_of_hasNoNegativeSelfExt (h0DLDb : D.HasNoNegativeSelfExt)
    (A : ComplexesObject D) (V : SchemesOver D.Y) (h : V ⟶ A.T) (n : ℤ) (hn : n < 0) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj A.E ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj A.E)⟦n⟧) :=
  h0DLDb (pullbackObject A h (relativelyPerfectBaseChange D h _ A.relativelyPerfect)) n hn

/-- **The glued object of a Čech covering.** Granted Stacks 0DLA (Čech case), 0DLD(b), 0DL1 with
0DL2, and 0DLC(1), the complexes of a Čech covering of `T` in `Complexes_{X/Y}` glue to an object
`⟨T, E⟩` of `Complexes_{X/Y}`, with morphisms from the `X i` over the members of the covering
whose two restrictions to every double overlap agree. -/
theorem CechCover.exists_glued (h0DLA : D.CechDescent) (h0DLDb : D.HasNoNegativeSelfExt)
    (hperf : D.RelativelyPerfectDescends) (hfib : D.NoNegativeFibreExtDescends)
    {T : SchemesOver D.Y} {I : Type (u + 1)} (C : CechCover T I) :
    ∃ (E : derivedModules B S hS (D.space T)) (hE : D.IsRelativelyPerfect T E)
      (hE' : D.HasNoNegativeFibreExt T E)
      (ψ : ∀ i, ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (C.a i))).obj E ⟶
        (C.X i).E) (hψ : ∀ i, IsIso (ψ i)),
      ∀ i j, (C.n i j).comp (⟨C.a i, ψ i, hψ i⟩ : ComplexesHom (C.X i) ⟨T, E, hE, hE'⟩) =
        (C.m i j).comp (⟨C.a j, ψ j, hψ j⟩ : ComplexesHom (C.X j) ⟨T, E, hE, hE'⟩) := by
  obtain ⟨E, ψ, hE, hcomp⟩ :=
    h0DLA T C (fun i => subsingleton_pull_shift_of_hasNoNegativeSelfExt h0DLDb (C.X i))
  have hp : D.IsRelativelyPerfect T E := hperf T (fun i => (C.X i).T) C.a C.covers E hE
    (fun i => isRelativelyPerfect_of_iso (ψ i) (C.X i).relativelyPerfect)
  have hf : D.HasNoNegativeFibreExt T E := hfib T (fun i => (C.X i).T) C.a C.covers E hp
    (fun i => hasNoNegativeFibreExt_of_iso (ψ i) (C.X i).noNegativeFibreExt)
  refine ⟨E, hp, hf, fun i => (ψ i).hom, fun i => inferInstance, fun i j => ?_⟩
  exact comp_mk_eq_comp_mk (X := ⟨T, E, hp, hf⟩) (C.n i j) (C.m i j) (ψ i).hom (ψ j).hom _ _
    (C.w i j) (hcomp i j)

open Functor in
/-- **Effectivity of descent data in `Complexes_{X/B}`, given its inputs as hypotheses.** Every
descent datum of `Complexes_{X/B}` relative to an fppf covering `{f i : V i ⟶ U}` is effective.

The test schemes `T_i` of the datum carry morphisms to `B` which glue to `T ⟶ B` over `U` by
Stacks 04P2 (`AlgebraicGeometry.Space.exists_comp_eq_of_compatible`); the restrictions of the
datum to the double and triple overlaps make a Čech covering of `T` in `Complexes_{X/B}` (the
gluing isomorphisms over a triple overlap lie over its identity by
`AlgebraicGeometry.Space.eq_id_of_tripleOverlap`), whose complexes glue to an object `⟨T, E⟩`
by `AlgebraicGeometry.Space.ComplexesSituation.CechCover.exists_glued`, and the morphisms into it
make the datum effective by `AlgebraicGeometry.Space.descentDatum_isEffective_of_compatible`. -/
theorem descentDatum_isEffective (h0DLA : D.CechDescent) (h0DLDb : D.HasNoNegativeSelfExt)
    (hperf : D.RelativelyPerfectDescends) (hfib : D.NoNegativeFibreExtDescends)
    {U : BigFppfOver B S hS} {I : Type (u + 1)} (V : I → BigFppfOver B S hS) (f : ∀ i, V i ⟶ U)
    (hcov : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS U)
    (Vij : I → I → BigFppfOver B S hS) (pr₁ : ∀ i j, Vij i j ⟶ V i)
    (pr₂ : ∀ i j, Vij i j ⟶ V j) (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (Vijk : I → I → I → BigFppfOver B S hS)
    (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j) (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
    (hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
    (q₁ : ∀ i j k, Vijk i j k ⟶ V i) (q₂ : ∀ i j k, Vijk i j k ⟶ V j)
    (q₃ : ∀ i j k, Vijk i j k ⟶ V k)
    (hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j)
    (hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j)
    (hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k)
    (𝔇 : DescentDatum (complexesFunctor D) V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
      q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    𝔇.IsEffective := by
  have hp := complexesFunctor_isFiberedInGroupoids D
  have : (complexesFunctor D).IsFibered := hp.isFibered
  have hx' : ∀ i, (𝔇.x i).T.left = V i := 𝔇.hx
  have hxr : ∀ i j, (𝔇.xrij i j).pt.T.left = Vij i j := fun i j => (𝔇.xrij i j).hpt
  have hxr' : ∀ i j, (𝔇.xrji i j).pt.T.left = Vij i j := fun i j => (𝔇.xrji i j).hpt
  -- the base map of a morphism over a given one
  have hfac : ∀ {W' V' : BigFppfOver B S hS} {x y : ComplexesObject D} (g : W' ⟶ V') (φ : x ⟶ y)
      (hx : x.T.left = W') (hy : y.T.left = V'), (complexesFunctor D).IsHomLift g φ →
      ((φ : ComplexesHom _ _).base.left = eqToHom hx ≫ g ≫ eqToHom hy.symm) :=
    fun g φ _ _ _ => IsHomLift.fac' (complexesFunctor D) g φ
  -- the base maps of the two morphisms out of a double overlap
  have hn : ∀ i j, ((𝔇.xrij i j).hom : ComplexesHom _ _).base.left =
      eqToHom (hxr i j) ≫ pr₁ i j ≫ eqToHom (hx' i).symm := fun i j =>
    hfac _ _ (hxr i j) (hx' i) (𝔇.xrij i j).isHomLift_hom
  have hn₂ : ∀ i j, ((𝔇.xrji i j).hom : ComplexesHom _ _).base.left =
      eqToHom (hxr' i j) ≫ pr₂ i j ≫ eqToHom (hx' j).symm := fun i j =>
    hfac _ _ (hxr' i j) (hx' j) (𝔇.xrji i j).isHomLift_hom
  have hφ : ∀ i j, ((𝔇.φ i j : _ ⟶ _) : ComplexesHom _ _).base.left =
      eqToHom ((hxr i j).trans (hxr' i j).symm) := by
    intro i j
    have := 𝔇.φ_fibreHom i j
    have h := (IsHomLift.eq_of_isHomLift (complexesFunctor D)
      (eqToHom (𝔇.xrij i j).hpt ≫ eqToHom (𝔇.xrji i j).hpt.symm) (𝔇.φ i j)).symm
    rwa [eqToHom_trans] at h
  have hm : ∀ i j, ((𝔇.φ i j ≫ (𝔇.xrji i j).hom : _ ⟶ _) : ComplexesHom _ _).base.left =
      eqToHom (hxr i j) ≫ pr₂ i j ≫ eqToHom (hx' j).symm := by
    intro i j
    change ((𝔇.φ i j : _ ⟶ _) : ComplexesHom _ _).base.left ≫
      ((𝔇.xrji i j).hom : ComplexesHom _ _).base.left = _
    rw [hφ, hn₂]
    simp
  -- the base map: glue the structure maps of the test schemes (Stacks 04P2)
  let b : ∀ i, (𝔇.x i).T.left ⟶ U := fun i => eqToHom (hx' i) ≫ f i
  have hcov' : Sieve.ofArrows (fun i => (𝔇.x i).T.left) b ∈ BigFppfOver.topology B S hS U := by
    refine (BigFppfOver.topology B S hS).superset_covering ?_ hcov
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    exact (Sieve.mem_ofArrows_iff _ _ (f i)).mpr ⟨i, eqToHom (hx' i).symm, by simp [b]⟩
  have hglue : ∀ i j (Z : BigFppfOver B S hS) (gi : Z ⟶ (𝔇.x i).T.left)
      (gj : Z ⟶ (𝔇.x j).T.left), gi ≫ b i = gj ≫ b j →
      (schemeSpaceFunctor B S hS).map gi ≫ (𝔇.x i).T.hom =
        (schemeSpaceFunctor B S hS).map gj ≫ (𝔇.x j).T.hom := by
    intro i j Z gi gj hgij
    have hl : (gi ≫ eqToHom (hx' i)) ≫ f i = (gj ≫ eqToHom (hx' j)) ≫ f j := by
      simpa [b] using hgij
    obtain ⟨l, egi, egj⟩ : ∃ l : Z ⟶ (𝔇.xrij i j).pt.T.left,
        gi = l ≫ ((𝔇.xrij i j).hom : ComplexesHom _ _).base.left ∧
        gj = l ≫ ((𝔇.φ i j ≫ (𝔇.xrji i j).hom : _ ⟶ _) : ComplexesHom _ _).base.left := by
      refine ⟨(hVij i j).lift _ _ hl ≫ eqToHom (hxr i j).symm, ?_, ?_⟩
      · rw [hn]; simp
      · rw [hm]; simp
    rw [egi, egj, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      CostructuredArrow.w, CostructuredArrow.w]
  obtain ⟨g, hg⟩ := exists_comp_eq_of_compatible D.Y _ b hcov' (fun i => (𝔇.x i).T.hom) hglue
  let T : SchemesOver D.Y := CostructuredArrow.mk g
  let a : ∀ i, (𝔇.x i).T ⟶ T := fun i => CostructuredArrow.homMk (b i) (hg i)
  -- the double overlaps
  have hpb : ∀ i j, IsPullback ((((𝔇.xrij i j).hom : ComplexesHom _ _).base)).left
      ((((𝔇.φ i j ≫ (𝔇.xrji i j).hom : _ ⟶ _) : ComplexesHom _ _).base)).left
      (a i).left (a j).left := by
    intro i j
    have := isPullback_eqToHom_conj (hxr i j) (hx' i) (hx' j) (hVij i j)
    rwa [← hn, ← hm] at this
  -- the triple overlaps
  have hwi : ∀ i j k, (𝔇.wi i j k).pt.T.left = Vijk i j k := fun i j k => (𝔇.wi i j k).hpt
  have hwj : ∀ i j k, (𝔇.wj i j k).pt.T.left = Vijk i j k := fun i j k => (𝔇.wj i j k).hpt
  have hwk : ∀ i j k, (𝔇.wk i j k).pt.T.left = Vijk i j k := fun i j k => (𝔇.wk i j k).hpt
  -- the base map of a canonical comparison of restrictions
  have hcompTo : ∀ {W' V' U' : BigFppfOver B S hS} (g' : W' ⟶ V') (f' : V' ⟶ U') {m' : W' ⟶ U'}
      (hm' : m' = g' ≫ f') {x : ComplexesObject D} {hx : x.T.left = U'}
      (xr : Restriction (complexesFunctor D) f' x hx)
      (xrW : Restriction (complexesFunctor D) m' x hx),
      ((Restriction.compTo (complexesFunctor D) g' f' hm' xr xrW : _ ⟶ _) :
        ComplexesHom _ _).base.left =
        eqToHom (show xrW.pt.T.left = W' from xrW.hpt) ≫ g' ≫
          eqToHom (show xr.pt.T.left = V' from xr.hpt).symm :=
    fun {_ _ _} g' f' {_} hm' {_ _} xr xrW =>
      hfac _ _ xrW.hpt xr.hpt (Restriction.isHomLift_compTo g' f' hm' xr xrW)
  -- the comparisons out of a triple overlap
  let c₁ : ∀ i j k, (𝔇.wi i j k).pt ⟶ (𝔇.xrij i j).pt := fun i j k =>
    Restriction.compTo (complexesFunctor D) (s₁₂ i j k) (pr₁ i j) (hq₁ i j k) (𝔇.xrij i j)
      (𝔇.wi i j k)
  let c₃ : ∀ i j k, (𝔇.wi i j k).pt ⟶ (𝔇.xrij i k).pt := fun i j k =>
    Restriction.compTo (complexesFunctor D) (𝔇.s₁₃ i j k) (pr₁ i k) (𝔇.hs₁₃₁ i j k).symm
      (𝔇.xrij i k) (𝔇.wi i j k)
  let cj : ∀ i j k, (𝔇.wj i j k).pt ⟶ (𝔇.xrij j k).pt := fun i j k =>
    Restriction.compTo (complexesFunctor D) (s₂₃ i j k) (pr₁ j k)
      ((hq₂ i j k).trans (hVijk i j k).w) (𝔇.xrij j k) (𝔇.wj i j k)
  let d : ∀ i j k, (𝔇.wi i j k).pt ⟶ (𝔇.xrij j k).pt := fun i j k => 𝔇.αij i j k ≫ cj i j k
  have e₁ : ∀ i j k, c₁ i j k ≫ (𝔇.xrij i j).hom = c₃ i j k ≫ (𝔇.xrij i k).hom :=
    fun i j k => (Restriction.compTo_hom _ _ _ _ _ _).trans
      (Restriction.compTo_hom _ _ _ _ _ _).symm
  have e₂ : ∀ i j k, c₁ i j k ≫ (𝔇.φ i j ≫ (𝔇.xrji i j).hom) = d i j k ≫ (𝔇.xrij j k).hom := by
    intro i j k
    calc c₁ i j k ≫ (𝔇.φ i j ≫ (𝔇.xrji i j).hom)
        = (c₁ i j k ≫ 𝔇.φ i j) ≫ (𝔇.xrji i j).hom := (Category.assoc _ _ _).symm
      _ = 𝔇.αij i j k ≫ (𝔇.wj i j k).hom := by
          rw [← 𝔇.αij_restr i j k, Category.assoc, Restriction.compTo_hom]
      _ = d i j k ≫ (𝔇.xrij j k).hom := by
          simp only [d, cj, Category.assoc, Restriction.compTo_hom]
  have e₃ : ∀ i j k, d i j k ≫ (𝔇.φ j k ≫ (𝔇.xrji j k).hom) =
      c₃ i j k ≫ (𝔇.φ i k ≫ (𝔇.xrji i k).hom) := by
    intro i j k
    calc d i j k ≫ (𝔇.φ j k ≫ (𝔇.xrji j k).hom)
        = 𝔇.αij i j k ≫ (cj i j k ≫ 𝔇.φ j k) ≫ (𝔇.xrji j k).hom := by
          simp only [d, Category.assoc]
      _ = (𝔇.αij i j k ≫ 𝔇.αjk i j k) ≫ (𝔇.wk i j k).hom := by
          rw [← 𝔇.αjk_restr i j k, Category.assoc, Restriction.compTo_hom, Category.assoc]
      _ = (c₃ i j k ≫ 𝔇.φ i k) ≫ (𝔇.xrji i k).hom := by
          rw [← 𝔇.αik_restr i j k, ← 𝔇.cocycle, Category.assoc, Restriction.compTo_hom]
      _ = c₃ i j k ≫ (𝔇.φ i k ≫ (𝔇.xrji i k).hom) := Category.assoc _ _ _
  -- the gluing isomorphisms over a triple overlap lie over its identity
  have hcl : ∀ {X Y Z : ComplexesObject D} (m : X ⟶ Y) (n : Y ⟶ Z),
      ((m ≫ n : X ⟶ Z) : ComplexesHom X Z).base.left =
        (m : ComplexesHom X Y).base.left ≫ (n : ComplexesHom Y Z).base.left := fun _ _ => rfl
  have hαij : ∀ i j k, ((𝔇.αij i j k : _ ⟶ _) : ComplexesHom _ _).base.left =
      eqToHom ((hwi i j k).trans (hwj i j k).symm) := by
    intro i j k
    have h₁ := congrArg (fun m : _ ⟶ _ => (m : ComplexesHom _ _).base.left) (𝔇.αij_restr i j k)
    have h₂ := congrArg (fun m : _ ⟶ _ => (m : ComplexesHom _ _).base.left) (𝔇.αjk_restr i j k)
    have h₃ := congrArg (fun m : _ ⟶ _ => (m : ComplexesHom _ _).base.left) (𝔇.αik_restr i j k)
    have h₄ := congrArg (fun m : _ ⟶ _ => (m : ComplexesHom _ _).base.left) (𝔇.cocycle i j k)
    simp only [hcl, hφ] at h₁ h₂ h₃ h₄
    rw [hcompTo (s₁₂ i j k) (pr₂ i j) _ (𝔇.xrji i j) (𝔇.wj i j k),
      hcompTo (s₁₂ i j k) (pr₁ i j) _ (𝔇.xrij i j) (𝔇.wi i j k)] at h₁
    rw [hcompTo (s₂₃ i j k) (pr₂ j k) _ (𝔇.xrji j k) (𝔇.wk i j k),
      hcompTo (s₂₃ i j k) (pr₁ j k) _ (𝔇.xrij j k) (𝔇.wj i j k)] at h₂
    rw [hcompTo (𝔇.s₁₃ i j k) (pr₂ i k) _ (𝔇.xrji i k) (𝔇.wk i j k),
      hcompTo (𝔇.s₁₃ i j k) (pr₁ i k) _ (𝔇.xrij i k) (𝔇.wi i j k)] at h₃
    have k₁ : ((𝔇.αij i j k : _ ⟶ _) : ComplexesHom _ _).base.left ≫ eqToHom (hwj i j k) ≫
        s₁₂ i j k = eqToHom (hwi i j k) ≫ s₁₂ i j k := by
      simpa using congrArg (· ≫ eqToHom (hxr' i j)) h₁
    have k₂ : ((𝔇.αjk i j k : _ ⟶ _) : ComplexesHom _ _).base.left ≫ eqToHom (hwk i j k) ≫
        s₂₃ i j k = eqToHom (hwj i j k) ≫ s₂₃ i j k := by
      simpa using congrArg (· ≫ eqToHom (hxr' j k)) h₂
    have k₃ : ((𝔇.αik i j k : _ ⟶ _) : ComplexesHom _ _).base.left ≫ eqToHom (hwk i j k) ≫
        𝔇.s₁₃ i j k = eqToHom (hwi i j k) ≫ 𝔇.s₁₃ i j k := by
      simpa using congrArg (· ≫ eqToHom (hxr' i k)) h₃
    have key := eq_id_of_tripleOverlap (hVij i j) (hVij j k) (hVijk i j k)
      ((𝔇.hs₁₃₁ i j k).trans (hq₁ i j k)) ((𝔇.hs₁₃₂ i j k).trans (hq₃ i j k))
      (γ := eqToHom (hwi i j k).symm ≫ ((𝔇.αij i j k : _ ⟶ _) : ComplexesHom _ _).base.left ≫
        eqToHom (hwj i j k))
      (γ' := eqToHom (hwj i j k).symm ≫ ((𝔇.αjk i j k : _ ⟶ _) : ComplexesHom _ _).base.left ≫
        eqToHom (hwk i j k))
      (γ'' := eqToHom (hwi i j k).symm ≫ ((𝔇.αik i j k : _ ⟶ _) : ComplexesHom _ _).base.left ≫
        eqToHom (hwk i j k))
      (by simp only [Category.assoc]; rw [k₁]; simp)
      (by simp only [Category.assoc]; rw [k₂]; simp)
      (by simp only [Category.assoc]; rw [k₃]; simp)
      (by rw [h₄]; simp)
    have := congrArg (fun t => eqToHom (hwi i j k) ≫ t ≫ eqToHom (hwj i j k).symm) key
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      Category.id_comp, eqToHom_trans_assoc] at this
    rw [this]
  -- the triple overlaps as test schemes over `Y`
  have hS₁₂ : ∀ i j k, (((c₁ i j k : _ ⟶ _) : ComplexesHom _ _).base).left =
      eqToHom (hwi i j k) ≫ s₁₂ i j k ≫ eqToHom (hxr i j).symm := fun i j k =>
    hcompTo (s₁₂ i j k) (pr₁ i j) _ (𝔇.xrij i j) (𝔇.wi i j k)
  have hS₂₃ : ∀ i j k, (((d i j k : _ ⟶ _) : ComplexesHom _ _).base).left =
      eqToHom (hwi i j k) ≫ s₂₃ i j k ≫ eqToHom (hxr j k).symm := by
    intro i j k
    change ((𝔇.αij i j k : _ ⟶ _) : ComplexesHom _ _).base.left ≫
      ((cj i j k : _ ⟶ _) : ComplexesHom _ _).base.left = _
    rw [hαij, hcompTo (s₂₃ i j k) (pr₁ j k) _ (𝔇.xrij j k) (𝔇.wj i j k)]
    simp
  have hpb₃ : ∀ i j k, IsPullback (((c₁ i j k : _ ⟶ _) : ComplexesHom _ _).base).left
      (((d i j k : _ ⟶ _) : ComplexesHom _ _).base).left
      ((((𝔇.φ i j ≫ (𝔇.xrji i j).hom : _ ⟶ _) : ComplexesHom _ _).base)).left
      ((((𝔇.xrij j k).hom : ComplexesHom _ _).base)).left := by
    intro i j k
    have := isPullback_eqToHom_conj' (hwi i j k) (hxr i j) (hxr j k) (hx' j) (hVijk i j k)
    rwa [← hS₁₂, ← hS₂₃, ← hm, ← hn] at this
  -- the Čech covering of the descent datum, and the glued object
  obtain ⟨E, hE, hE', ψ, hψ, hc⟩ := CechCover.exists_glued h0DLA h0DLDb hperf hfib
    (⟨𝔇.x, a, hcov', fun i j => (𝔇.xrij i j).pt, fun i j => (𝔇.xrij i j).hom,
      fun i j => 𝔇.φ i j ≫ (𝔇.xrji i j).hom, hpb, fun i j k => (𝔇.wi i j k).pt, c₁, d, c₃,
      hpb₃, e₁, e₂, e₃⟩ : CechCover T I)
  refine descentDatum_isEffective_of_compatible 𝔇 (⟨T, E, hE, hE'⟩ : ComplexesObject D) rfl
    (fun i => (⟨a i, ψ i, hψ i⟩ : ComplexesHom (𝔇.x i) ⟨T, E, hE, hE'⟩)) (fun i => ?_) hc
  have : (complexesFunctor D).IsHomLift (f i)
      ((⟨a i, ψ i, hψ i⟩ : ComplexesHom (𝔇.x i) ⟨T, E, hE, hE'⟩) : 𝔇.x i ⟶ _) := by
    refine IsHomLift.of_fac' _ _ _ (𝔇.hx i) rfl ?_
    change eqToHom (hx' i) ≫ f i = eqToHom (hx' i) ≫ f i ≫ 𝟙 U
    rw [Category.comp_id]
  exact hp.isStronglyCartesian_homLift (f i) _

/-- **Stacks 0DLH, given its inputs as hypotheses.** `Complexes_{X/Y}` is a stack in groupoids
over `(Sch/S)_fppf`. The `Isom` presheaves are sheaves by Stacks 0DLG through Stacks 045G
(`h0DLG`), and every descent datum is effective by
`AlgebraicGeometry.Space.ComplexesSituation.descentDatum_isEffective`, which glues the complexes by
Stacks 0DLA and checks the two conditions of `Complexes_{X/Y}` on the glued complex by Stacks 0DL1
with 0DL2 and by Stacks 0DLC(1); the sieve-indexed descent data of Stacks 026F are read as
family-indexed ones by `CategoryTheory.Functor.SieveDescentDatum.isEffective_of_toFamilyDatum`.

The hypotheses are these results, each at its Stacks content:
* `h0DLG`: Stacks 0DLG;
* `h0DLA`: Stacks 0DLA (Čech case);
* `h0DLDb`: Stacks 0DLD(b) at `V = T`;
* `hperf`: Stacks 0DL1 with 0DL2;
* `hfib`: Stacks 0DLC(1). -/
theorem complexesFunctor_isStackInGroupoids_of_pending
    (h0DLG : Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D)
        (complexesFunctor_isFiberedInGroupoids D)))
    (h0DLA : D.CechDescent) (h0DLDb : D.HasNoNegativeSelfExt)
    (hperf : D.RelativelyPerfectDescends) (hfib : D.NoNegativeFibreExtDescends) :
    (complexesFunctor D).IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS) := by
  refine Stack.isStackInGroupoids_of_hasRepresentableDiagonal B S hS _ h0DLG ?_
  intro U R hR 𝔇
  have : (CatFiberedInGroupoids.mk (complexesBasedCategory D)
      (complexesFunctor_isFiberedInGroupoids D)).val.p.IsFibered :=
    (complexesFunctor_isFiberedInGroupoids D).isFibered
  exact 𝔇.isEffective_of_toFamilyDatum <| descentDatum_isEffective h0DLA h0DLDb hperf hfib
    (Functor.SieveDescentDatum.arrowSrc R)
    (Functor.SieveDescentDatum.arrowHom R) (by rwa [Sieve.ofArrows_category])
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end ComplexesSituation

end AlgebraicGeometry.Space

end
