module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ExtendedAlternatingCech
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AugmentationContractible
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.OrderedComplex
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Acyclicity of the extended alternating Čech complex away from the equations

The extended alternating Čech complex associated to finitely many global functions is acyclic
after restriction to the complement of their common zero locus — that is, to the union of their
principal opens.

## Main definitions

* `AlgebraicGeometry.ExtendedAlternatingCech.moduleSectionsFunctor`: sections over an open, as a
  functor from modules on a scheme to abelian groups.

## Main results

* `AlgebraicGeometry.ExtendedAlternatingCech.stalkExact_of_sectionExact`: a complex of modules on
  a scheme is exact at a stalk if its complexes of sections are exact over a neighbourhood basis
  of the point.
* `AlgebraicGeometry.ExtendedAlternatingCech.acyclic_on_equationsComplement`: acyclicity after
  restriction to that open complement.

## Implementation notes

The complement of the closed subscheme cut out by the equations is expressed as the union of
their principal opens, and restriction to this open is pullback along its inclusion.

## References

* [Stacks Project, Tag 0G7K](https://stacks.math.columbia.edu/tag/0G7K)
* [Stacks Project, Tag 01FI](https://stacks.math.columbia.edu/tag/01FI)
* [Stacks Project, Tag 0G6T](https://stacks.math.columbia.edu/tag/0G6T)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ExtendedAlternatingCech

private def addCommGrpIsoOfEquiv {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) : AddCommGrpCat.of A ≅ AddCommGrpCat.of B where
  hom := AddCommGrpCat.ofHom e.toAddMonoidHom
  inv := AddCommGrpCat.ofHom e.symm.toAddMonoidHom
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

private def uliftAddEquiv {A : Type*} [AddCommGroup A] : A ≃+ ULift.{0} A where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Sections over an open, as a functor from modules on a scheme to abelian groups. -/
public def moduleSectionsFunctor {X : Scheme.{u}} (V : X.Opens) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  Scheme.Modules.toPresheaf X ⋙
    (evaluation ((Opens (↑X.toPresheafedSpace))ᵒᵖ) AddCommGrpCat.{u}).obj (Opposite.op V)

/-- Sections over an open preserve zero morphisms. -/
public instance moduleSectionsFunctor_preservesZeroMorphisms
    {X : Scheme.{u}} (V : X.Opens) :
    (moduleSectionsFunctor V).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

private noncomputable def localOrderedCechAugment
    {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    (V : X.Opens) (i : Fin c) (hV : V ≤ X.basicOpen (f i)) :
    CochainComplex AddCommGrpCat.{u} ℕ := by
  let T := X.toPresheafedSpace
  let opens : Fin c → Opens T := fun j => V ⊓ X.basicOpen (f j)
  let P := (Scheme.Modules.toPresheaf X).obj F
  let A := Stacks.Cech.orderedCechComplex opens P
  let α := Stacks.Cech.orderedCechAugmentation T P opens (fun _ => inf_le_left)
  have hi : opens i = V := inf_eq_left.mpr hV
  let hcontract := Stacks.Cech.orderedCechComplex_augment_homotopyEquiv_zero_of_eq
    T P opens (fun _ => inf_le_left) i hi
  exact A.augment α hcontract.choose

private lemma localOrderedCechAugment_d_zero_one
    {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    (V : X.Opens) (i : Fin c) (hV : V ≤ X.basicOpen (f i)) :
    (localOrderedCechAugment f F V i hV).d 0 1 =
      Stacks.Cech.orderedCechAugmentation (X.toPresheafedSpace : TopCat)
        ((Scheme.Modules.toPresheaf X).obj F)
        (fun j : Fin c => V ⊓ X.basicOpen (f j)) (fun _ => inf_le_left) := by
  dsimp [localOrderedCechAugment]
  rfl

private lemma localOrderedCechAugment_d_succ_succ
    {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    (V : X.Opens) (i : Fin c) (hV : V ≤ X.basicOpen (f i)) (p : ℕ) :
    (localOrderedCechAugment f F V i hV).d (p + 1) (p + 1 + 1) =
      (Stacks.Cech.orderedCechComplex
        (fun j : Fin c => V ⊓ X.basicOpen (f j))
        ((Scheme.Modules.toPresheaf X).obj F)).d p (p + 1) := by
  dsimp [localOrderedCechAugment]
  rfl

private noncomputable def sectionComplexIso
    {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    (V : X.Opens) (i : Fin c) (hV : V ≤ X.basicOpen (f i)) :
    (((moduleSectionsFunctor V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (data f F).complex) ≅ localOrderedCechAugment f F V i hV := by
  let d := data f F
  let E := moduleSectionsFunctor V
  let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj d.complex
  let target := localOrderedCechAugment f F V i hV
  let e0 : K.X 0 ≅ target.X 0 :=
    (E.mapIso d.zeroIso) ≪≫ addCommGrpIsoOfEquiv uliftAddEquiv
  let es (p : ℕ) := addCommGrpIsoOfEquiv (d.sectionsIso p V)
  let components : ∀ n : ℕ, K.X n ≅ target.X n := fun
    | 0 => e0
    | p + 1 => es p
  refine HomologicalComplex.Hom.isoOfComponents components ?_
  intro p q hpq
  have hq : q = p + 1 := (show p + 1 = q by simpa [ComplexShape.up_Rel] using hpq).symm
  subst q
  cases p with
  | zero =>
      dsimp [components, target]
      rw [localOrderedCechAugment_d_zero_one]
      ext x
      unfold CechCochains.OrdCochain at *
      funext s
      dsimp [e0, es, addCommGrpIsoOfEquiv, uliftAddEquiv,
        moduleSectionsFunctor, Stacks.Cech.orderedCechAugmentation,
        Stacks.Cech.cechDegreeZeroRestriction]
      exact (d.differential_zero V x s).symm
  | succ p =>
      dsimp [components, target]
      rw [localOrderedCechAugment_d_succ_succ, Stacks.Cech.orderedCechComplex_d]
      ext x
      unfold CechCochains.OrdCochain at *
      funext s
      dsimp [es, addCommGrpIsoOfEquiv, moduleSectionsFunctor]
      exact (congrFun (d.differential_succ p V x) s).symm

private lemma sectionComplexAcyclic_on_basicOpen
    {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)
    (V : X.Opens) (i : Fin c) (hV : V ≤ X.basicOpen (f i)) :
    (((moduleSectionsFunctor V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (data f F).complex).Acyclic := by
  let hcontract := Stacks.Cech.orderedCechComplex_augment_homotopyEquiv_zero_of_eq
    X.toPresheafedSpace ((Scheme.Modules.toPresheaf X).obj F)
    (fun j : Fin c => V ⊓ X.basicOpen (f j)) (fun _ => inf_le_left) i
    (inf_eq_left.mpr hV)
  let h : HomotopyEquiv (localOrderedCechAugment f F V i hV)
      (HomologicalComplex.zero : CochainComplex AddCommGrpCat.{u} ℕ) :=
    Classical.choice hcontract.choose_spec
  let e := sectionComplexIso f F V i hV
  let h' := (HomotopyEquiv.ofIso e).trans h
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hz : Limits.IsZero
      ((HomologicalComplex.zero : CochainComplex AddCommGrpCat.{u} ℕ).homology n) :=
    ShortComplex.isZero_homology_of_isZero_X₂
      ((HomologicalComplex.zero : CochainComplex AddCommGrpCat.{u} ℕ).sc n)
      (Limits.isZero_zero AddCommGrpCat.{u})
  exact Limits.IsZero.of_iso hz (h'.toHomologyIso n)

/-- **Exactness of a complex of modules on a scheme at a stalk, from exactness of its complexes
of sections over a neighbourhood basis of the point**: if every open neighbourhood of `x`
contains an open neighbourhood `W` of `x` over which the complex of sections is exact at `n`, then
the stalk at `x` of the short complex of `K` at `n` is exact. -/
public theorem stalkExact_of_sectionExact
    {X : Scheme.{u}} (K : CochainComplex X.Modules ℕ) (x : X) (n : ℕ)
    (hsec : ∀ W₀ : X.Opens, x ∈ W₀ → ∃ W : X.Opens, W ≤ W₀ ∧ x ∈ W ∧
      (((moduleSectionsFunctor W).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).ExactAt n) :
    (SheafOfModules.stalkShortComplex
      (structureSheafRing X.toRingedSpace) (K.sc n)
        x).Exact := by
  let S := K.sc n
  let T := SheafOfModules.stalkShortComplex
    (structureSheafRing X.toRingedSpace) S x
  let P₁ := Scheme.Modules.presheaf S.X₁
  let P₂ := Scheme.Modules.presheaf S.X₂
  let P₃ := Scheme.Modules.presheaf S.X₃
  rw [ShortComplex.ab_exact_iff]
  intro z hz
  obtain ⟨V, hxV, s, hs⟩ := P₂.exists_germ_eq z
  have hgz : P₃.germ V x hxV (S.g.app V s) = 0 := by
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      S.g.mapPresheaf) z = 0 at hz
    rw [← hs, TopCat.Presheaf.stalkFunctor_map_germ_apply] at hz
    exact hz
  obtain ⟨W₀, hxW₀, iW₀V, iV, hs0⟩ := P₃.germ_eq x hxV hxV
    (S.g.app V s) 0 (by simpa using hgz)
  obtain ⟨W, hWW₀, hxW, hL⟩ := hsec W₀ hxW₀
  let iWW₀ : W ⟶ W₀ := homOfLE hWW₀
  let iWV : W ⟶ V := iWW₀ ≫ iW₀V
  let E := moduleSectionsFunctor W
  let L := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  have hFunc : Function.Exact (L.sc n).f (L.sc n).g :=
    (ShortComplex.ab_exact_iff_function_exact _).mp hL
  let sW := P₂.map iWV.op s
  have hs0W : P₃.map iWV.op (S.g.app V s) = 0 := by
    have hs0' := congrArg (fun z => P₃.map iWW₀.op z) hs0
    calc
      P₃.map iWV.op (S.g.app V s) =
          P₃.map iWW₀.op (P₃.map iW₀V.op (S.g.app V s)) := by simp [iWV]
      _ = P₃.map iWW₀.op (P₃.map iV.op 0) := hs0'
      _ = 0 := by simp
  have hsW : (L.sc n).g sW = 0 := by
    have hn := congrArg (fun φ => φ s) (S.g.mapPresheaf.naturality iWV.op)
    have hn' : (S.g.app W) sW = P₃.map iWV.op (S.g.app V s) := by
      simpa only [sW, ConcreteCategory.comp_apply,
        Scheme.Modules.mapPresheaf_app] using hn
    change (S.g.app W) sW = 0
    rw [hn']
    exact hs0W
  obtain ⟨tW, htW⟩ := Set.mem_range.mp ((hFunc sW).mp hsW)
  let tW' : ↑(P₁.obj (op W)) := by
    change ↑((K.X ((ComplexShape.up ℕ).prev n)).presheaf.obj (op W))
    exact tW
  refine ⟨P₁.germ W x hxW tW', ?_⟩
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      S.f.mapPresheaf) (P₁.germ W x hxW tW') = z
  have htW'' : (S.f.app W) tW' = sW := htW
  have hgerm := TopCat.Presheaf.stalkFunctor_map_germ_apply
    W x hxW S.f.mapPresheaf tW'
  rw [hgerm, Scheme.Modules.mapPresheaf_app, htW'', P₂.germ_res_apply, hs]

/-- The extended alternating Čech complex is acyclic off the common zero locus
of the global equations. -/
@[stacks 0G7K]
public theorem acyclic_on_equationsComplement
    {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules) :
    (((Scheme.Modules.pullback (⨆ i, X.basicOpen (f i)).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (data f F).complex).Acyclic := by
  let U : X.Opens := ⨆ i, X.basicOpen (f i)
  let j := U.ι
  let K := (data f F).complex
  let K' := ((Scheme.Modules.pullback j).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  rw [HomologicalComplex.acyclic_iff]
  intro n
  apply (SheafOfModules.exact_iff_stalkShortComplex_exact
    (structureSheafRing U.toScheme.toRingedSpace)
      (K'.sc n)).2
  intro x
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp x.2
  have hOrig :
      (SheafOfModules.stalkShortComplex
        (structureSheafRing X.toRingedSpace) (K.sc n)
          (j x)).Exact := by
    have hxj : j x ∈ X.basicOpen (f i) := hxi
    refine stalkExact_of_sectionExact K (j x) n fun W₀ hxW₀ => ?_
    exact ⟨W₀ ⊓ X.basicOpen (f i), inf_le_left, ⟨hxW₀, hxj⟩,
      sectionComplexAcyclic_on_basicOpen f F _ i inf_le_right n⟩
  let P := Scheme.Modules.toPresheaf U.toScheme ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let Q := Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j x)
  let F₁ := Scheme.Modules.pullback j ⋙ P
  let F₂ := Q
  let e₁ := Functor.isoWhiskerRight
    (Scheme.Modules.restrictFunctorIsoPullback j).symm P
  let e₂ := Scheme.Modules.restrictStalkNatIso j x
  let e := e₁ ≪≫ e₂
  let S := K.sc n
  let eS : S.map F₁ ≅ S.map F₂ := ShortComplex.isoMk
    (e.app S.X₁) (e.app S.X₂) (e.app S.X₃)
    (by simpa [F₁, F₂, Q, Scheme.Modules.toPresheaf_map] using (e.hom.naturality S.f).symm)
    (by simpa [F₁, F₂, Q, Scheme.Modules.toPresheaf_map] using (e.hom.naturality S.g).symm)
  change (S.map F₁).Exact
  exact (ShortComplex.exact_iff_of_iso eS).2 hOrig

end AlgebraicGeometry.ExtendedAlternatingCech
