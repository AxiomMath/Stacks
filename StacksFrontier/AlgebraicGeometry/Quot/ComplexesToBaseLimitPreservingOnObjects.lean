module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackProved
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects

/-!
# The projection `Complexes_{X/B} ⟶ 𝒮_B` is limit preserving on objects

For a proper, flat, finitely presented morphism `f : X ⟶ B` of algebraic spaces over a scheme `S`,
the projection `Complexes_{X/B} ⟶ 𝒮_B`, `(T, g, E) ↦ (T, g)`, is limit preserving on objects. No
hypothesis on `B` is needed: the structure morphism `T_i ⟶ B` of a stage is part of the data of
the object of `𝒮_B` over it. Consequently the structure morphism `Complexes_{X/B} ⟶ B` is locally
of finite presentation once `Complexes_{X/B}` is algebraic.

## Main results

* `isLimitPreservingOnObjects_complexesToBaseCFG`: the projection `Complexes_{X/B} ⟶ 𝒮_B` is
  limit preserving on objects.
* `isLocallyOfFinitePresentation_complexesStructureMorphism`:
  if `Complexes_{X/B}` is an algebraic stack, its structure morphism to `B` is locally of finite
  presentation.

## References

* [Stacks Project, Tag 0DPX](https://stacks.math.columbia.edu/tag/0DPX)
* [Stacks Project, Tag 0DLJ](https://stacks.math.columbia.edu/tag/0DLJ)
* [Stacks Project, Tag 0DLI](https://stacks.math.columbia.edu/tag/0DLI)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u w

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory instModulesHasDerivedCategory

/-- **The projection `Complexes_{X/B} ⟶ 𝒮_B` is limit preserving on objects.** Let
`T = lim T_j` be a cofiltered limit of affine schemes of the site, taken in schemes, and let
`(T, g, E)` be an object of `Complexes_{X/B}` over `T` whose structure morphism `g : T ⟶ B`
factors as `T ⟶ T_i ⟶ B`. Then `E` is, up to isomorphism, the derived pullback of an object
`(T_j, T_j ⟶ T_i ⟶ B, E_j)` of `Complexes_{X/B}` over a later stage, compatibly with the given
factorisation. No hypothesis on `B` is needed. -/
theorem isLimitPreservingOnObjects_complexesToBaseCFG (D : ComplexesSituation B S hS) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS _ _ (complexesToBaseCFG D) := by
  intro I _ _ Dg c hc i y x γ hγ
  let incl := BigAffineFppf.inclusion B S hS
  let p := complexesFunctor D
  let q := (baseBasedCategory D.Y).p
  have hp : p.IsFiberedInGroupoids := (complexesCFG D).isFiberedInGroupoids
  have hq : q.IsFiberedInGroupoids := (baseCFG D.Y).isFiberedInGroupoids
  obtain ⟨y, hy⟩ := y
  obtain ⟨L, ⟨⟨⟩⟩, g⟩ := y
  change L = incl.obj (Dg.obj i) at hy
  subst hy
  obtain ⟨⟨⟨Tl, Tr, Th⟩, E, hperf, hext⟩, hA⟩ := x
  change Tl = _ at hA
  subst hA
  let A : ComplexesObject D := ⟨⟨_, Tr, Th⟩, E, hperf, hext⟩
  let γ₀ : A.T ⟶ CostructuredArrow.mk g := γ.down
  have hγl : γ₀.left = eqToHom rfl ≫ incl.map (c.π.app i) := by
    have : q.IsHomLift (incl.map (c.π.app i)) γ := hγ.toIsHomLift
    have h := IsHomLift.fac' q (incl.map (c.π.app i)) γ
    change γ₀.left = eqToHom rfl ≫ incl.map (c.π.app i) ≫ eqToHom rfl at h
    simpa only [eqToHom_refl, Category.comp_id] using h
  have hg : A.T.hom = (schemeSpaceFunctor B S hS).map
      (eqToHom rfl ≫ incl.map (c.π.app i)) ≫ g := by
    rw [← hγl]
    exact (CostructuredArrow.w γ₀).symm
  let F := D.stageDiagram Dg i g
  let d := D.stageCone Dg c i g A.T rfl hg
  have hd := D.isLimitStageCone Dg hc i g A.T rfl hg
  obtain ⟨hobj, -, -⟩ := D.relativelyPerfectColimit_baseChanges (Over i) F d hd
    (fun j => (Dg.obj j.left).2) c.pt.2
  obtain ⟨k, Ek, hEk, ⟨e⟩⟩ := hobj E hperf
  obtain ⟨W, hW⟩ := D.fibreExtLocusIsOpen_of_existsNegativeExtLocus
    (existsNegativeExtLocus_proved B S hS) (F.obj k) Ek (Dg.obj k.left).2 hEk
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
  have hδ : p.IsHomLift (incl.map (c.π.app j)) (δ : A ⟶ xj) := by
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    show eqToHom rfl ≫ _ = eqToHom rfl ≫ _ ≫ eqToHom rfl
    simp only [eqToHom_refl]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hcart : ∀ {R T : BigFppfOver B S hS} (f : R ⟶ T) {a b : ComplexesObject D} (φ : a ⟶ b),
      p.IsHomLift f φ → p.IsStronglyCartesian f φ := by
    intro R T f a b φ hφ
    have hsc := hp.isStronglyCartesian φ
    subst_hom_lift p f φ
    exact hsc
  let γ' : ULiftHom.objUp xj.T ⟶ (ULiftHom.objUp (CostructuredArrow.mk g) : BaseObjects D.Y) :=
    ULift.up (CostructuredArrow.homMk (incl.map (Dg.map j'.hom)) rfl)
  have hγ' : q.IsStronglyCartesian (incl.map (Dg.map j'.hom)) γ' := hq.isStronglyCartesian γ'
  have hsq : (complexesToBase D).map (δ : A ⟶ xj) ≫ γ' = (complexesToBase D).map (𝟙 A) ≫ γ := by
    refine ULift.ext (CostructuredArrow.hom_ext _ _ ?_)
    show (d.π.app j' ≫ γ'.down).left = (𝟙 A.T ≫ γ₀).left
    show (eqToHom rfl ≫ incl.map (c.π.app j)) ≫ incl.map (Dg.map j'.hom) = (𝟙 A.T ≫ γ₀).left
    rw [Category.id_comp, hγl, Category.assoc, ← Functor.map_comp, Cone.w]
  exact ⟨j, j'.hom, ⟨xj, rfl⟩, ⟨A, rfl⟩, δ, 𝟙 A, γ', hcart _ _ hδ, IsHomLift.id rfl,
    IsIso.id _, hγ', hsq⟩

/-- **The structure morphism `Complexes_{X/B} ⟶ B` is locally of finite presentation**, given
that `Complexes_{X/B}` is an algebraic stack (`h`). -/
theorem isLocallyOfFinitePresentation_complexesStructureMorphism (D : ComplexesSituation B S hS)
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (complexesBasedCategory D)) :
    Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (complexesStructureMorphism D h) :=
  Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isLimitPreservingOnObjects B S hS _
    ((shrinkHomsComparison _ h).isLimitPreservingOnObjects_conj _ _
      (isLimitPreservingOnObjects_complexesToBaseCFG D))

end AlgebraicGeometry.Space.ComplexesSituation

end
