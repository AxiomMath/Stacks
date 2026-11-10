module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseChangeGlobal

/-!
# Base change of relative dualizing complexes (Stacks 0E2Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite StrictlyPerfect
open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  (hpb : IsPullback g' f' f g) [Flat f] [LocallyOfFinitePresentation f]
  (D : DiagonalOpen f) (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
  (hw : w ≫ D.ι = D'.ι ≫ pullbackMapOfIsPullback hpb)
  {V : S.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)
  {V' : S'.Opens} (hV' : IsAffineOpen V') (hV'V : V' ≤ g ⁻¹ᵁ V)

omit [Flat f] [LocallyOfFinitePresentation f] in
include hpb in
/-- **The charts cover `X'`**: every point of `X'` lies in some `U' = g'⁻¹(U) ∩ f'⁻¹(V')` with
`V ⊆ S`, `U ⊆ f⁻¹(V)` and `V' ⊆ g⁻¹(V)` affine. -/
theorem exists_mem_chartBaseChange (x : X') :
    ∃ (V : S.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U) (_ : U ≤ f ⁻¹ᵁ V)
      (V' : S'.Opens) (_ : IsAffineOpen V') (_ : V' ≤ g ⁻¹ᵁ V),
      x ∈ chartBaseChange (g' := g') (f' := f') (U := U) (V' := V') := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.base (g'.base x))) isOpen_univ
  have h₁ : f'.base x ∈ g ⁻¹ᵁ V := by
    change (f' ≫ g).base x ∈ V
    rwa [← hpb.w]
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hV'V⟩ := S'.isBasis_affineOpens.exists_subset_of_mem_open
    h₁ (g ⁻¹ᵁ V).isOpen
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show g'.base x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
  exact ⟨V, hV, U, hU, hUV, V', hV', hV'V, ⟨hxU, hxV'⟩⟩

/-- The isomorphism `Lb^* ⋙ La^* ≅ Ld^* ⋙ Lc^*` induced by a commuting square `c ≫ d = a ≫ b`. -/
private def pullCommIso {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D}
    (h : c ≫ d = a ≫ b) : pull b ⋙ pull a ≅ pull d ⋙ pull c :=
  Stacks.Duality.UpperShriekDuality.pullCompIso a b (a ≫ b) rfl ≪≫
    (Stacks.Duality.UpperShriekDuality.pullCompIso c d (a ≫ b) h).symm

include hpb hw hV hU hUV hV' hV'V in
/-- **The restricted base-changed map is a generator on each chart.** Let `(K_U, ξ_U)` be the
restriction of `(K, ξ)` to `U` (through any identifications `eU`, `pU`), a relative dualizing
complex for `U ⟶ S` with `ξ_U` a generator. Then the restriction to `W'_{U'}` of the base change
`φ ≫ Lw^*ξ ≫ ψ` (through any identifications `e'`, `p'`) is a generator. -/
theorem isPostcompGenerator_restrict_baseChange (K : DerivedCategory X.Modules)
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (eU : (pull (D.restrictInclusion U.ι)).obj D.diagonalObject ≅ (D.restrict U.ι).diagonalObject)
    (pU : (pull (D.restrictInclusion U.ι)).obj (D.derivedPullbackProj K) ≅
      (D.restrict U.ι).derivedPullbackProj ((pull U.ι).obj K))
    (hKU : IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.restrict U.ι)
      ((pull U.ι).obj K) (eU.inv ≫ (pull (D.restrictInclusion U.ι)).map ξ ≫ pU.hom))
    (hgU : Dualizing.IsPostcompGenerator
      (eU.inv ≫ (pull (D.restrictInclusion U.ι)).map ξ ≫ pU.hom))
    (φ : D'.diagonalObject ≅ (pull w).obj D.diagonalObject)
    (ψ : (pull w).obj (D.derivedPullbackProj K) ≅ D'.derivedPullbackProj (baseChangeComplex g' K))
    {L'' : DerivedCategory
      (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).toScheme.Modules}
    (e' : (pull (D'.restrictInclusion (chartBaseChange (g' := g') (f' := f') (U := U)
      (V' := V')).ι)).obj D'.diagonalObject ≅
        (D'.restrict (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι).diagonalObject)
    (p' : (pull (D'.restrictInclusion (chartBaseChange (g' := g') (f' := f') (U := U)
      (V' := V')).ι)).obj (D'.derivedPullbackProj (baseChangeComplex g' K)) ≅
        (D'.restrict (chartBaseChange (g' := g') (f' := f') (U := U)
          (V' := V')).ι).derivedPullbackProj L'') :
    Dualizing.IsPostcompGenerator (e'.inv ≫
      (pull (D'.restrictInclusion
        (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι)).map
          (φ.hom ≫ (pull w).map ξ ≫ ψ.hom) ≫ p'.hom) := by
  let j := D.restrictInclusion U.ι
  let j' := D'.restrictInclusion (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι
  let wU := chartBaseChangeW hpb D D' w hw (U := U) (V' := V')
  -- `Lw_U^*(Lj^*ξ)` is a generator
  have h₁ : Dualizing.IsPostcompGenerator ((pull wU).map ((pull j).map ξ)) :=
    (Dualizing.IsPostcompGenerator.map_conj_inv_iff (pull wU) eU pU ((pull j).map ξ)).1
      (isPostcompGenerator_chart hpb D D' w hw hV hU hUV hV' hV'V _ _ hKU hgU)
  -- transport along `Lw_U^* Lj^* ≅ Lj'^* Lw^*`
  have h₃ : Dualizing.IsPostcompGenerator ((pull j').map ((pull w).map ξ)) :=
    Dualizing.IsPostcompGenerator.map_natIso (f := ξ)
      (pullCommIso (chartBaseChangeW_restrictInclusion hpb D D' w hw).symm) h₁
  exact (Dualizing.IsPostcompGenerator.conj_iff e' p' _).2
    ((Dualizing.IsPostcompGenerator.map_conj_iff (pull j') φ ψ ((pull w).map ξ)).2 h₃)

include hpb hV hU hUV hV' hV'V in
/-- **`R ℰom(𝒪_{U'}, L pr₁^*(L(g')^*K)|_{U'}|_{W'_{U'}}) ≅ 𝒪_{U'}[0]`**, for the restriction to `U`
of a relative dualizing complex `(K, ξ)`. -/
theorem nonempty_diagonalExactSupport_restrict_baseChange (K : DerivedCategory X.Modules)
    (ξU : (D.restrict U.ι).diagonalObject ⟶ (D.restrict U.ι).derivedPullbackProj ((pull U.ι).obj K))
    (hKU : IsRelativeDualizingComplex (U.ι ≫ f)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) (D.restrict U.ι)
      ((pull U.ι).obj K) ξU) :
    Nonempty ((D'.restrict (chartBaseChange (g' := g') (f' := f') (U := U)
      (V' := V')).ι).diagonalExactSupport
        ((pull (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι).obj
          (baseChangeComplex g' K)) ≅
        structureSingle (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).toScheme) := by
  obtain ⟨e⟩ := nonempty_diagonalExactSupport_chart hpb D D' hV hU hUV hV' hV'V _ _ hKU
  let U' := chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')
  let gU := chartBaseChangeHom (g' := g') (f' := f') (U := U) (V' := V')
  let c : (pull U'.ι).obj (baseChangeComplex g' K) ≅ baseChangeComplex gU ((pull U.ι).obj K) :=
    (pullCommIso chartBaseChangeHom_ι).app K
  exact ⟨(D'.restrict U'.ι).diagQuotient.derivedSheafHomExactSupport.mapIso
    ((pull (D'.restrict U'.ι).proj).mapIso c) ≪≫ e⟩

omit [Flat f] [LocallyOfFinitePresentation f] in
include hpb in
/-- **The diagonal condition on `W'` from the charts `U'`.** -/
theorem isIso_diagonalAction_of_charts (L : DerivedCategory X'.Modules)
    (ζ : D'.diagonalObject ⟶ D'.derivedPullbackProj L)
    (h : ∀ (V : S.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U)
      (_ : U ≤ f ⁻¹ᵁ V) (V' : S'.Opens) (_ : IsAffineOpen V') (_ : V' ≤ g ⁻¹ᵁ V),
      IsIso ((pull (D'.restrictInclusion
        (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι)).map
          (D'.diagonalAction L ζ))) :
    IsIso (D'.diagonalAction L ζ) := by
  let I := Σ' (V : S.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U)
    (_ : U ≤ f ⁻¹ᵁ V) (V' : S'.Opens) (_ : IsAffineOpen V'), V' ≤ g ⁻¹ᵁ V
  refine D'.isIso_diagonalAction_of_cover L ζ (I := I)
    (fun i => D'.restrictInclusion (chartBaseChange (g' := g') (f' := f') (U := i.2.2.1)
      (V' := i.2.2.2.2.2.1)).ι) (fun x => ?_) (fun i => h _ i.2.1 _ i.2.2.2.1 i.2.2.2.2.1 _
        i.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2)
  obtain ⟨V, hV, U, hU, hUV, V', hV', hV'V, hx⟩ := exists_mem_chartBaseChange hpb x
  obtain ⟨y, rfl⟩ : x ∈ Set.range
      (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι.base := by
    rwa [Scheme.Opens.range_ι]
  refine ⟨⟨V, hV, U, hU, hUV, V', hV', hV'V⟩, ⟨(D'.restrict _).diag.base y, ?_⟩⟩
  exact congrArg (fun k => k.base y) (D'.restrictDiag_restrictInclusion
    (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι)

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
