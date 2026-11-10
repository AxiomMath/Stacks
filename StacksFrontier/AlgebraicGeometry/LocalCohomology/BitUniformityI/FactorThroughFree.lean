module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import StacksFrontier.Algebra.Module.IProjective
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Support.ShortExactPushout
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Tor.Vanishing
public import StacksFrontier.RingTheory.UniversallyExact
public import StacksCore.Tactic.StacksAttribute

/-!
# A Tor-vanishing criterion for factorization through a free module

Let `M ⟶ M'` be a map of modules, with `M` finitely presented. If its induced map on first Tor
is zero after evaluation at every module, then the map factors through a free module.

## Main results

* `factor_through_free_of_tor_one_map_eq_zero` gives the free-module factorization.

## Implementation notes

The first Tor groups and their functorial maps are expressed using the canonical bifunctor
`CategoryTheory.Tor'`. Thus the vanishing hypothesis is independent of choices of resolutions
and lifts. Factorization through a free module is expressed by the existing predicate
`FactorsThroughFree`. The connecting map of the Tor long exact sequence is built here as
`torBoundary`, from the homology long exact sequence of the complex obtained by tensoring a
short exact sequence with a projective resolution of the second variable.

## References

* [Stacks Project, Tag 0G9T](https://stacks.math.columbia.edu/tag/0G9T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.ShortComplex
open Stacks.Tor.SixTermSequence (homologyZeroIso homologyFunctor_map_comp_homologyZeroIso_hom)
open Stacks.Tor.FunctorSequence (homologyFunctor_map_comp_isoLeftDerivedObj_inv)

universe u

/-- The homology functor and `HomologicalComplex.homologyMap` agree up to the canonical
equality of their values. -/
private lemma homologyFunctor_map_cast_left
    {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    {ι : Type*} {c : ComplexShape ι} (i : ι) [CategoryWithHomology C]
    {K K' : HomologicalComplex C c} (f : K ⟶ K') :
    (HomologicalComplex.homologyFunctor C c i).map f ≫
        eqToHom (HomologicalComplex.homologyFunctor_obj C c i K') =
      eqToHom (HomologicalComplex.homologyFunctor_obj C c i K) ≫
        HomologicalComplex.homologyMap f i := by
  have hK := HomologicalComplex.homologyFunctor_obj C c i K
  have hK' := HomologicalComplex.homologyFunctor_obj C c i K'
  have hconj : (HomologicalComplex.homologyFunctor C c i).map f =
      eqToHom hK ≫ HomologicalComplex.homologyMap f i ≫ eqToHom hK'.symm :=
    (CategoryTheory.conj_eqToHom_iff_heq _ _ hK hK'.symm).2 (by
      simp only [HomologicalComplex.homologyFunctor_map]
      exact HEq.rfl)
  have hcancel : eqToHom hK'.symm ≫ eqToHom hK' = 𝟙 _ := by
    have hp : hK'.symm.trans hK' = rfl := Subsingleton.elim _ _
    calc
      eqToHom hK'.symm ≫ eqToHom hK' = eqToHom (hK'.symm.trans hK') :=
        eqToHom_trans _ _
      _ = 𝟙 _ := by rw [hp]; simp
  rw [hconj]
  calc
    (eqToHom hK ≫ HomologicalComplex.homologyMap f i ≫ eqToHom hK'.symm) ≫
        eqToHom hK' = eqToHom hK ≫ HomologicalComplex.homologyMap f i ≫
          (eqToHom hK'.symm ≫ eqToHom hK') := by simp only [Category.assoc]
    _ = eqToHom hK ≫ HomologicalComplex.homologyMap f i := by
      rw [hcancel]
      simp

/-- The mirror of `homologyFunctor_map_cast_left`, with the equalities on the other side. -/
private lemma homologyFunctor_map_cast_right
    {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    {ι : Type*} {c : ComplexShape ι} (i : ι) [CategoryWithHomology C]
    {K K' : HomologicalComplex C c} (f : K ⟶ K') :
    HomologicalComplex.homologyMap f i ≫
        eqToHom (HomologicalComplex.homologyFunctor_obj C c i K').symm =
      eqToHom (HomologicalComplex.homologyFunctor_obj C c i K).symm ≫
        (HomologicalComplex.homologyFunctor C c i).map f := by
  have hK := HomologicalComplex.homologyFunctor_obj C c i K
  have hK' := HomologicalComplex.homologyFunctor_obj C c i K'
  have hconj : (HomologicalComplex.homologyFunctor C c i).map f =
      eqToHom hK ≫ HomologicalComplex.homologyMap f i ≫ eqToHom hK'.symm :=
    (CategoryTheory.conj_eqToHom_iff_heq _ _ hK hK'.symm).2 (by
      simp only [HomologicalComplex.homologyFunctor_map]
      exact HEq.rfl)
  have hcancel : eqToHom hK.symm ≫ eqToHom hK = 𝟙 _ := by
    have hp : hK.symm.trans hK = rfl := Subsingleton.elim _ _
    calc
      eqToHom hK.symm ≫ eqToHom hK = eqToHom (hK.symm.trans hK) :=
        eqToHom_trans _ _
      _ = 𝟙 _ := by rw [hp]; simp
  rw [hconj]
  calc
    HomologicalComplex.homologyMap f i ≫ eqToHom hK'.symm =
        (eqToHom hK.symm ≫ eqToHom hK) ≫ HomologicalComplex.homologyMap f i ≫
          eqToHom hK'.symm := by rw [hcancel]; simp
    _ = eqToHom hK.symm ≫
        (eqToHom hK ≫ HomologicalComplex.homologyMap f i ≫ eqToHom hK'.symm) := by
          simp only [Category.assoc]

/-- The connecting map `Tor₁(X₃, N) ⟶ X₁ ⊗ N` of a short exact sequence. -/
private noncomputable def torBoundary
    {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 1).obj S.X₃).obj N ⟶ S.X₁ ⊗ N := by
  let T : ShortComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
    ShortComplex.mk ((tensoringLeft (ModuleCat.{u} R)).map S.f)
      ((tensoringLeft (ModuleCat.{u} R)).map S.g) (by
        rw [← Functor.map_comp, S.zero, Functor.map_zero])
  let P := projectiveResolution N
  let U : ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
    ShortComplex.mk ((NatTrans.mapHomologicalComplex T.f (ComplexShape.down ℕ)).app P.complex)
      ((NatTrans.mapHomologicalComplex T.g (ComplexShape.down ℕ)).app P.complex) (by
        rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, T.zero]
        ext n
        simp)
  have hU : U.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact U (fun n ↦ by
    have hflat : Module.Flat R (P.complex.X n) := inferInstance
    exact hS.map_of_exact (tensorRight (P.complex.X n)))
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
  let h3 := HomologicalComplex.homologyFunctor_obj (ModuleCat.{u} R)
    (ComplexShape.down ℕ) 1 U.X₃
  let h1 := HomologicalComplex.homologyFunctor_obj (ModuleCat.{u} R)
    (ComplexShape.down ℕ) 0 U.X₁
  exact (P.isoLeftDerivedObj (T.X₃) 1).hom ≫ eqToHom h3 ≫ hU.δ 1 0 hrel ≫
    eqToHom h1.symm ≫
      (((P.isoLeftDerivedObj T.X₁ 0).symm) ≪≫
        (Functor.leftDerivedZeroIsoSelf T.X₁).app N).hom

/-- `torBoundary` sits in the six-term exact sequence of a short exact sequence tensored with
`N`. -/
private theorem torBoundary_exact
    {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (N : ModuleCat.{u} R) :
    (ComposableArrows.mk₅
      (((Tor (ModuleCat.{u} R) 1).map S.f).app N)
      (((Tor (ModuleCat.{u} R) 1).map S.g).app N)
      (torBoundary hS N)
      (((tensoringLeft (ModuleCat.{u} R)).map S.f).app N)
      (((tensoringLeft (ModuleCat.{u} R)).map S.g).app N)).Exact := by
  let T : ShortComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
    ShortComplex.mk ((tensoringLeft (ModuleCat.{u} R)).map S.f)
      ((tensoringLeft (ModuleCat.{u} R)).map S.g) (by
        rw [← Functor.map_comp, S.zero, Functor.map_zero])
  let P := projectiveResolution N
  let U : ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
    ShortComplex.mk ((NatTrans.mapHomologicalComplex T.f (ComplexShape.down ℕ)).app P.complex)
      ((NatTrans.mapHomologicalComplex T.g (ComplexShape.down ℕ)).app P.complex) (by
        rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, T.zero]
        ext n
        simp)
  have hU : U.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact U (fun n ↦ by
    have hflat : Module.Flat R (P.complex.X n) := inferInstance
    exact hS.map_of_exact (tensorRight (P.complex.X n)))
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
  exact ComposableArrows.exact_of_iso (ComposableArrows.isoMk₅
    (P.isoLeftDerivedObj T.X₁ 1).symm (P.isoLeftDerivedObj T.X₂ 1).symm
    (P.isoLeftDerivedObj T.X₃ 1).symm
    (homologyZeroIso T.X₁ P) (homologyZeroIso T.X₂ P) (homologyZeroIso T.X₃ P)
    (homologyFunctor_map_comp_isoLeftDerivedObj_inv T.f P 1)
    (homologyFunctor_map_comp_isoLeftDerivedObj_inv T.g P 1)
    (Iso.inv_hom_id_assoc (P.isoLeftDerivedObj T.X₃ 1) _).symm
    (homologyFunctor_map_comp_homologyZeroIso_hom T.f P)
    (homologyFunctor_map_comp_homologyZeroIso_hom T.g P))
    (HomologicalComplex.HomologySequence.composableArrows₅_exact hU 1 0 hrel)

/-- `torBoundary` is natural in the short exact sequence. -/
private theorem torBoundary_naturality
    {R : Type u} [CommRing R] {S S' : ShortComplex (ModuleCat.{u} R)}
    (φ : S ⟶ S') (hS : S.ShortExact) (hS' : S'.ShortExact)
    (N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 1).map φ.τ₃).app N ≫ torBoundary hS' N =
      torBoundary hS N ≫ ((tensoringLeft (ModuleCat.{u} R)).map φ.τ₁).app N := by
  let T : ShortComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
    ShortComplex.mk ((tensoringLeft (ModuleCat.{u} R)).map S.f)
      ((tensoringLeft (ModuleCat.{u} R)).map S.g) (by
        rw [← Functor.map_comp, S.zero, Functor.map_zero])
  let T' : ShortComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
    ShortComplex.mk ((tensoringLeft (ModuleCat.{u} R)).map S'.f)
      ((tensoringLeft (ModuleCat.{u} R)).map S'.g) (by
        rw [← Functor.map_comp, S'.zero, Functor.map_zero])
  let P := projectiveResolution N
  let U : ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
    ShortComplex.mk ((NatTrans.mapHomologicalComplex T.f (ComplexShape.down ℕ)).app P.complex)
      ((NatTrans.mapHomologicalComplex T.g (ComplexShape.down ℕ)).app P.complex) (by
        rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, T.zero]
        ext n
        simp)
  let U' : ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
    ShortComplex.mk ((NatTrans.mapHomologicalComplex T'.f (ComplexShape.down ℕ)).app P.complex)
      ((NatTrans.mapHomologicalComplex T'.g (ComplexShape.down ℕ)).app P.complex) (by
        rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, T'.zero]
        ext n
        simp)
  have hU : U.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact U (fun n ↦ by
    have hflat : Module.Flat R (P.complex.X n) := inferInstance
    exact hS.map_of_exact (tensorRight (P.complex.X n)))
  have hU' : U'.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact U' (fun n ↦ by
      have hflat : Module.Flat R (P.complex.X n) := inferInstance
      exact hS'.map_of_exact (tensorRight (P.complex.X n)))
  let ψT : T ⟶ T' :=
    { τ₁ := (tensoringLeft (ModuleCat.{u} R)).map φ.τ₁
      τ₂ := (tensoringLeft (ModuleCat.{u} R)).map φ.τ₂
      τ₃ := (tensoringLeft (ModuleCat.{u} R)).map φ.τ₃
      comm₁₂ := by
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₂]
      comm₂₃ := by
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂₃] }
  let ψ : U ⟶ U' :=
    { τ₁ := (NatTrans.mapHomologicalComplex ψT.τ₁ (ComplexShape.down ℕ)).app P.complex
      τ₂ := (NatTrans.mapHomologicalComplex ψT.τ₂ (ComplexShape.down ℕ)).app P.complex
      τ₃ := (NatTrans.mapHomologicalComplex ψT.τ₃ (ComplexShape.down ℕ)).app P.complex
      comm₁₂ := by
        have h := congrArg (fun α ↦ NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ))
          ψT.comm₁₂
        have h' := congrArg (fun α ↦ α.app P.complex) h
        change (NatTrans.mapHomologicalComplex ψT.τ₁ (ComplexShape.down ℕ)).app P.complex ≫
            (NatTrans.mapHomologicalComplex T'.f (ComplexShape.down ℕ)).app P.complex =
          (NatTrans.mapHomologicalComplex T.f (ComplexShape.down ℕ)).app P.complex ≫
            (NatTrans.mapHomologicalComplex ψT.τ₂ (ComplexShape.down ℕ)).app P.complex
        simpa only [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] using h'
      comm₂₃ := by
        have h := congrArg (fun α ↦ NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ))
          ψT.comm₂₃
        have h' := congrArg (fun α ↦ α.app P.complex) h
        change (NatTrans.mapHomologicalComplex ψT.τ₂ (ComplexShape.down ℕ)).app P.complex ≫
            (NatTrans.mapHomologicalComplex T'.g (ComplexShape.down ℕ)).app P.complex =
          (NatTrans.mapHomologicalComplex T.g (ComplexShape.down ℕ)).app P.complex ≫
            (NatTrans.mapHomologicalComplex ψT.τ₃ (ComplexShape.down ℕ)).app P.complex
        simpa only [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] using h' }
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
  have hδ := HomologicalComplex.HomologySequence.δ_naturality ψ hU hU' 1 0 hrel
  have hTorMap : (NatTrans.leftDerived ψT.τ₃ 1).app N ≫
      (P.isoLeftDerivedObj T'.X₃ 1).hom =
    (P.isoLeftDerivedObj T.X₃ 1).hom ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 1).map
        ((NatTrans.mapHomologicalComplex ψT.τ₃ (ComplexShape.down ℕ)).app P.complex) := by
    rw [P.leftDerived_app_eq ψT.τ₃ 1]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hzero := homologyFunctor_map_comp_homologyZeroIso_hom ψT.τ₁ P
  dsimp only [U, U'] at hδ hzero hTorMap
  let h3 := HomologicalComplex.homologyFunctor_obj (ModuleCat.{u} R)
    (ComplexShape.down ℕ) 1 U.X₃
  let h3' := HomologicalComplex.homologyFunctor_obj (ModuleCat.{u} R)
    (ComplexShape.down ℕ) 1 U'.X₃
  let h1 := HomologicalComplex.homologyFunctor_obj (ModuleCat.{u} R)
    (ComplexShape.down ℕ) 0 U.X₁
  let h1' := HomologicalComplex.homologyFunctor_obj (ModuleCat.{u} R)
    (ComplexShape.down ℕ) 0 U'.X₁
  have hTorMap' := hTorMap
  change (NatTrans.leftDerived ψT.τ₃ 1).app N ≫ (P.isoLeftDerivedObj T'.X₃ 1).hom =
      (P.isoLeftDerivedObj T.X₃ 1).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 1).map
          ψ.τ₃ at hTorMap'
  have hcast3 := homologyFunctor_map_cast_left (C := ModuleCat.{u} R) 1 ψ.τ₃
  change (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 1).map ψ.τ₃ ≫
      eqToHom h3' = eqToHom h3 ≫ HomologicalComplex.homologyMap ψ.τ₃ 1 at hcast3
  have hcast1 := homologyFunctor_map_cast_right (C := ModuleCat.{u} R) 0 ψ.τ₁
  change HomologicalComplex.homologyMap ψ.τ₁ 0 ≫ eqToHom h1'.symm =
      eqToHom h1.symm ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).map
          ψ.τ₁ at hcast1
  change (NatTrans.leftDerived ψT.τ₃ 1).app N ≫ (P.isoLeftDerivedObj T'.X₃ 1).hom ≫
      eqToHom h3' ≫ hU'.δ 1 0 hrel ≫ eqToHom h1'.symm ≫ (homologyZeroIso T'.X₁ P).hom =
    (P.isoLeftDerivedObj T.X₃ 1).hom ≫ eqToHom h3 ≫ hU.δ 1 0 hrel ≫
      eqToHom h1.symm ≫ (homologyZeroIso T.X₁ P).hom ≫ ψT.τ₁.app N
  calc
    _ = (P.isoLeftDerivedObj T.X₃ 1).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 1).map ψ.τ₃ ≫
        eqToHom h3' ≫ hU'.δ 1 0 hrel ≫ eqToHom h1'.symm ≫ (homologyZeroIso T'.X₁ P).hom := by
          rw [reassoc_of% hTorMap']
    _ = (P.isoLeftDerivedObj T.X₃ 1).hom ≫ eqToHom h3 ≫
        HomologicalComplex.homologyMap ψ.τ₃ 1 ≫ hU'.δ 1 0 hrel ≫
        eqToHom h1'.symm ≫ (homologyZeroIso T'.X₁ P).hom := rfl
    _ = (P.isoLeftDerivedObj T.X₃ 1).hom ≫ eqToHom h3 ≫
        hU.δ 1 0 hrel ≫ HomologicalComplex.homologyMap ψ.τ₁ 0 ≫
        eqToHom h1'.symm ≫ (homologyZeroIso T'.X₁ P).hom := by
          rw [reassoc_of% hδ.symm]
    _ = (P.isoLeftDerivedObj T.X₃ 1).hom ≫ eqToHom h3 ≫ hU.δ 1 0 hrel ≫
        eqToHom h1.symm ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).map
          ψ.τ₁ ≫ (homologyZeroIso T'.X₁ P).hom := rfl
    _ = (P.isoLeftDerivedObj T.X₃ 1).hom ≫ eqToHom h3 ≫ hU.δ 1 0 hrel ≫
        eqToHom h1.symm ≫ (homologyZeroIso T.X₁ P).hom ≫ ψT.τ₁.app N := by
          rw [hzero]

/-- **Stacks Project, Tag 0G9T.** A map from a finitely presented module which induces the zero
map on `Tor₁` with every module factors through a free module. -/
@[stacks 0G9T]
lemma factor_through_free_of_tor_one_map_eq_zero
    {R : Type u} [CommRing R] {M M' : ModuleCat.{u} R} (f : M ⟶ M')
    [Module.FinitePresentation R M]
    (hf : ∀ N : ModuleCat.{u} R,
      ((Tor' (ModuleCat.{u} R) 1).map f).app N = 0) :
    FactorsThroughFree f.hom := by
  classical
  let C := ModuleCat.{u} R
  let F : Type u := M' →₀ R
  let ε : F →ₗ[R] M' := Finsupp.linearCombination R id
  have hε : Function.Surjective ε := fun x ↦ ⟨Finsupp.single x 1, by
    change (Finsupp.linearCombination R id) (Finsupp.single x 1) = x
    simp⟩
  obtain ⟨n, m, p, r, hp, hpr⟩ := Module.FinitePresentation.exists_fin' R M
  obtain ⟨l, hl⟩ := Module.projective_lifting_property ε (f.hom.comp p) hε
  let S := p.shortComplexKer
  let i : S.X₁ →ₗ[R] (Fin n → R) := S.f.hom
  let aLin : S.X₁ →ₗ[R] LinearMap.ker ε := LinearMap.codRestrict _ (l.comp i) fun x ↦
    LinearMap.mem_ker.2 <| (LinearMap.congr_fun hl (i x)).trans
      (by simp [i, S, LinearMap.shortComplexKer])
  let a : S.X₁ ⟶ ModuleCat.of R (LinearMap.ker ε) := ModuleCat.ofHom (R := R) aLin
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hp
  obtain ⟨E, j, i', q, hi'q, hPO, hjq, hE⟩ :=
    CategoryTheory.exists_shortExact_pushout S.zero hS a
  let T := ε.shortComplexKer
  have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hε
  have ha : S.f ≫ ModuleCat.ofHom l = a ≫ ModuleCat.ofHom (LinearMap.ker ε).subtype := by
    ext x
    rfl
  let u : E ⟶ ModuleCat.of R F := hPO.desc (ModuleCat.ofHom l)
      (ModuleCat.ofHom (LinearMap.ker ε).subtype) ha
  have hju : j ≫ u = ModuleCat.ofHom l :=
    hPO.inl_desc (ModuleCat.ofHom l) (ModuleCat.ofHom (LinearMap.ker ε).subtype) ha
  have hiu : i' ≫ u = ModuleCat.ofHom (LinearMap.ker ε).subtype :=
    hPO.inr_desc (ModuleCat.ofHom l) (ModuleCat.ofHom (LinearMap.ker ε).subtype) ha
  let φ : (ShortComplex.mk i' q hi'q) ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := u
      τ₃ := ModuleCat.ofHom f.hom
      comm₁₂ := by
        simp only [Category.id_comp]
        change T.f = i' ≫ u
        exact hiu.symm
      comm₂₃ := by
        apply hPO.hom_ext
        · rw [← Category.assoc, hju, ← Category.assoc, hjq]
          change ModuleCat.ofHom l ≫ ModuleCat.ofHom ε =
            S.g ≫ ModuleCat.ofHom f.hom
          apply ModuleCat.hom_ext
          simpa [S] using hl
        · rw [← Category.assoc, hiu, ← Category.assoc, hi'q, zero_comp]
          simpa [T] using T.zero }
  have hfTor (N : C) : ((Tor C 1).map φ.τ₃).app N = 0 := by
    have hnat := congrArg (fun α ↦ α.app N)
      (Tor_iso_Tor'.naturality R 1 f)
    rw [NatTrans.comp_app] at hnat
    have hcomp : ((Tor C 1).map f).app N ≫
        (Tor_iso_Tor'.app R 1 M').hom.app N = 0 := by
      calc
        _ = (Tor_iso_Tor'.app R 1 M).hom.app N ≫ ((Tor' C 1).map f).app N := by
          simpa [C] using hnat
        _ = 0 := by rw [hf N]; simp
    exact (cancel_mono ((Tor_iso_Tor'.app R 1 M').hom.app N)).1 (by simpa [φ] using hcomp)
  have hboundary (N : C) : torBoundary hE N = 0 := by
    have h := torBoundary_naturality φ hE hT N
    rw [hfTor N, zero_comp] at h
    simpa [φ] using h.symm
  have hTensorInjective (N : C) : Function.Injective (LinearMap.rTensor N i'.hom) := by
    have hmono : Mono (((tensoringLeft C).map (ShortComplex.mk i' q hi'q).f).app N) :=
      ((torBoundary_exact hE N).exact 2 (by norm_num)).mono_g (hboundary N)
    change Function.Injective (LinearMap.rTensor N i'.hom)
    exact (ModuleCat.mono_iff_injective _).mp hmono
  have hExact : Function.Exact (i'.hom) q.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hE.exact
  have hi' : Function.Injective i'.hom :=
    (ModuleCat.mono_iff_injective _).mp hE.mono_f
  have hq : Function.Surjective q.hom :=
    (ModuleCat.epi_iff_surjective _).mp hE.epi_g
  obtain ⟨s, hs⟩ :=
    (Function.Exact.split_iff_forall_rTensor_injective hExact hi' hq).2 (by
      intro Q instQ modQ
      let N : C := ModuleCat.of R Q
      change Function.Injective (LinearMap.rTensor (↑N) i'.hom)
      exact hTensorInjective N)
  have hfactor : f.hom = ε.comp (u.hom.comp s) := by
    have hdiag : ε.comp u.hom = f.hom.comp q.hom := ModuleCat.hom_ext_iff.mp φ.comm₂₃
    calc
      f.hom = f.hom.comp (q.hom.comp s) := by rw [hs, LinearMap.comp_id]
      _ = ε.comp (u.hom.comp s) := by rw [← LinearMap.comp_assoc, ← hdiag, LinearMap.comp_assoc]
  exact ⟨M', u.hom.comp s, ε, hfactor⟩
