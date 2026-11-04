module

public import StacksFrontier.Algebra.Homology.InjectiveQuasiIsoMap
public import StacksFrontier.Algebra.Module.Injective.SelfInjectiveFiniteProjective
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FunctorTrace
public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# Traces along a non-exact functor on bounded below complexes of injectives

Let `R` be a ring which is injective as a module over itself, `Φ : Mod_R ⥤ Mod_S` an additive
functor carrying finite projective modules to finite projective modules, and `θ : Φ ⟶ Φ` a
natural endomorphism. Let `X` be a bounded below complex of injective `R`-modules whose class in
`D(R)` is perfect, and `g : X ⟶ X` a chain map. Then `Φ(X)` is perfect over `S` and

`Tr_S(θ_X ∘ Φ(g) | Φ(X)) = Φ♮(Tr_R(g | X))`.

The functor `Φ` need not be exact: a finite projective representative `P` of `X` has injective
terms because `R` is self-injective, so the comparison `P ⟶ X` is a quasi-isomorphism between
bounded below complexes of injectives and stays one after applying `Φ`. Out of `P`, which is
K-projective, the endomorphism `g` is represented up to homotopy, and the trace on `Φ(P)` is
computed by `CategoryTheory.FilteredDerived.perfectDerivedTrace_functor`.

## Main results

* `CategoryTheory.FilteredDerived.isPerfect_map_of_injective_of_baer`: `Φ(X)` is perfect.
* `CategoryTheory.FilteredDerived.perfectDerivedTrace_map_of_injective_of_baer`: the trace
  identity.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v u' w

namespace CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [Ring R] {S : Type u'} [Ring S]
  (Φ : ModuleCat.{max u v} R ⥤ ModuleCat.{w} S) [Φ.Additive] (hΦ : PreservesFiniteProjective Φ)

/-- The data used to compute traces on `Φ(X)`: a finite projective representative `P` of `X`
and a quasi-isomorphism `P ⟶ X` which stays a quasi-isomorphism after applying `Φ`. -/
private lemma exists_representative (hR : Module.Baer R R)
    (X : CochainComplex (ModuleCat.{max u v} R) ℤ) (d : ℤ) [X.IsStrictlyGE d]
    [∀ n, Injective (X.X n)] (hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj X)) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (_hP : finiteProjectiveComplex R P)
      (u : P ⟶ X), IsIso (DerivedCategory.Q.map u) ∧
        QuasiIso ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map u) ∧ P.IsKProjective := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isPerfect_iff R _).1 hX
  have hKP : P.IsKProjective := isKProjective_obj R
    ⟨(HomotopyCategory.quotient _ _).obj P,
      (finiteProjectiveComplex.{u, max u v} R).strictMap_obj _ hP⟩
  obtain ⟨u, hu⟩ := StacksDraft.PseudoCoherence.exists_chainMap_of_isKProjective P X e.hom
  refine ⟨P, hP, u, hu ▸ inferInstance, ?_, hKP⟩
  obtain ⟨a, ha⟩ := hP.1.1
  have : P.IsStrictlyGE a := ha
  have : P.IsStrictlyGE (min a d) := P.isStrictlyGE_of_ge _ a (min_le_left _ _)
  have : X.IsStrictlyGE (min a d) := X.isStrictlyGE_of_ge _ d (min_le_right _ _)
  have : ∀ n, Injective (P.X n) := fun n => by
    let := (hP.2 n).1
    let := (hP.2 n).2
    exact ModuleCat.injective_of_finite_projective hR (P.X n)
  have : QuasiIso u := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, hu]
    infer_instance
  exact CochainComplex.quasiIso_map_of_injective Φ u (min a d)

include hΦ in
/-- **An additive functor preserving finite projective modules carries a perfect bounded below
complex of injective modules over a self-injective ring to a perfect complex.** -/
theorem isPerfect_map_of_injective_of_baer (hR : Module.Baer R R)
    (X : CochainComplex (ModuleCat.{max u v} R) ℤ) (d : ℤ) [X.IsStrictlyGE d]
    [∀ n, Injective (X.X n)] (hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj X)) :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) := by
  obtain ⟨P, hP, u, -, hu, -⟩ := exists_representative Φ hR X d hX
  exact (isPerfect_iff S _).2 ⟨_, finiteProjectiveComplex_map Φ hΦ P hP,
    ⟨asIso (DerivedCategory.Q.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map u))⟩⟩

/-- **Functoriality of the trace along a non-exact functor**, for a perfect bounded below
complex `X` of injective modules over a self-injective ring `R` and an endomorphism `g` of `X`:
`Tr_S(θ_X ∘ Φ(g) | Φ(X)) = Φ♮(Tr_R(g | X))`. -/
theorem perfectDerivedTrace_map_of_injective_of_baer (θ : Φ ⟶ Φ) (hR : Module.Baer R R)
    (X : CochainComplex (ModuleCat.{max u v} R) ℤ) (d : ℤ) [X.IsStrictlyGE d]
    [∀ n, Injective (X.X n)] (hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj X))
    (g : X ⟶ X) :
    perfectDerivedTrace S ⟨_, isPerfect_map_of_injective_of_baer Φ hΦ hR X d hX⟩
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app X ≫
          (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g)) =
      functorTraceMap Φ θ hΦ (perfectDerivedTrace R ⟨_, hX⟩ (DerivedCategory.Q.map g)) := by
  obtain ⟨P, hP, u, hu, hΦu, hKP⟩ := exists_representative Φ hR X d hX
  let e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj X := asIso (DerivedCategory.Q.map u)
  obtain ⟨g', hg'⟩ := StacksDraft.PseudoCoherence.exists_chainMap_of_isKProjective P P
    (e.hom ≫ DerivedCategory.Q.map g ≫ e.inv)
  have hcomm : DerivedCategory.Q.map (g' ≫ u) = DerivedCategory.Q.map (u ≫ g) := by
    rw [Functor.map_comp, hg']
    simp [e]
  obtain ⟨H⟩ := StacksDraft.PseudoCoherence.homotopic_of_Q_map_eq _ _ hcomm
  let e' : DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) :=
    asIso (DerivedCategory.Q.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map u))
  refine perfectDerivedTrace_functor Φ θ hΦ ⟨_, hX⟩ _ P hP e g' hg' ⟨_, _⟩ _ e' ?_
  rw [← cancel_mono e'.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hH : DerivedCategory.Q.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (g' ≫ u)) =
      DerivedCategory.Q.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (u ≫ g)) :=
    DerivedCategory.Q_map_eq_of_homotopy (h := Φ.mapHomotopy H)
  have hnat := (NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).naturality u
  simp only [e', asIso_hom, Functor.map_comp, Category.assoc] at hH ⊢
  rw [hH, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← hnat]

end CategoryTheory.FilteredDerived
