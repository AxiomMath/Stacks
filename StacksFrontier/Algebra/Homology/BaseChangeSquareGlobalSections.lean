module

public import StacksFrontier.Algebra.Homology.RightDerivedCoEdgeAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeResolution

/-!
# The base change map on cohomology, read on global sections

This file is the homological algebra behind the identification, over affine bases, of the base
change map of higher direct images of **Stacks 073K**, part (1), with the comparison map of part
(2). Everything is stated for abstract abelian categories, so that the geometric statement is a
single instance of it.

The data is a commutative square of "spaces", recorded by its four direct image functors
`f_*, g_*, f'_*, g'_*`, the left adjoints `g^*` and `(g')^*` of the two horizontal ones, a
comparison `κ : g'_* ⋙ f_* ≅ f'_* ⋙ g_*` of the two composite direct images, four "global
sections" functors `Γ` with values in categories of modules, four restriction functors `r` between
those, the comparisons `Γ_Y ∘ k_* ≅ r_k ∘ Γ_X` of **Stacks 0732**, and a comparison `σ` of the two
composite restrictions.  The one hypothesis tying them together is that **Stacks 0732** is
compatible with `κ` and `σ` around the square.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.baseChange_square_component`: in each degree, the
  degree-zero base change map (the mate of `κ`), read on global sections, is the pullback along
  `g'`.
* `Stacks.Cohomology.RightDerivedCoEdge.baseChange_homology_globalSections`: the morphism of
  cohomology objects induced by the base change map on complexes, transposed and read on global
  sections, is the pullback map `c` on cohomology, up to isomorphisms on both sides.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {MX MY MX' MY' EA EA' EX EX' : Type*} [Category* MX] [Category* MY] [Category* MX']
  [Category* MY'] [Category* EA] [Category* EA'] [Category* EX] [Category* EX']
  [Abelian MX] [Abelian MY] [Abelian MX'] [Abelian MY'] [Abelian EA] [Abelian EA'] [Abelian EX]
  [Abelian EX']
  {fs : MX ⥤ MY} {gs : MY' ⥤ MY} {fs' : MX' ⥤ MY'} {gs' : MX' ⥤ MX}
  {gu : MY ⥤ MY'} {gu' : MX ⥤ MX'} (adj : gu ⊣ gs) (adj' : gu' ⊣ gs')
  {ΓY : MY ⥤ EA} {ΓY' : MY' ⥤ EA'} {ΓX : MX ⥤ EX} {ΓX' : MX' ⥤ EX'}
  {rf : EX ⥤ EA} {rg : EA' ⥤ EA} {rg' : EX' ⥤ EX} {rf' : EX' ⥤ EA'}
  (κ : gs' ⋙ fs ≅ fs' ⋙ gs) (eF : fs ⋙ ΓY ≅ ΓX ⋙ rf) (eG : gs ⋙ ΓY ≅ ΓY' ⋙ rg)
  (eF' : fs' ⋙ ΓY' ≅ ΓX' ⋙ rf') (eG' : gs' ⋙ ΓX ≅ ΓX' ⋙ rg') (σ : rg' ⋙ rf ≅ rf' ⋙ rg)

omit [Abelian MX] [Abelian MY] [Abelian MX'] [Abelian MY'] [Abelian EA] [Abelian EA'] [Abelian EX]
  [Abelian EX'] in
/-- **The degreewise square.**  If **Stacks 0732** is compatible with `κ` and `σ` around the
square, then for `ψ : (g')^*K ⟶ L`, reading on global sections of `Y'` the unit of `g^* ⊣ g_*` at
`f_*K` followed by the mate of `κ` and `f'_*ψ`, and then reading the result on `X'`, is reading on
`X` the unit of `(g')^* ⊣ g'_*` followed by `g'_*ψ`, and then reading the result on `X'`. -/
theorem baseChange_square_component
    (hD0 : ∀ N : MX', ΓY.map (κ.hom.app N) ≫ eG.hom.app (fs'.obj N) ≫ rg.map (eF'.hom.app N) =
      eF.hom.app (gs'.obj N) ≫ rf.map (eG'.hom.app N) ≫ σ.hom.app (ΓX'.obj N))
    (K : MX) {L : MX'} (ψ : gu'.obj K ⟶ L) :
    ΓY.map (adj.unit.app (fs.obj K) ≫
        gs.map ((Stacks.Cohomology.BaseChange.mate adj adj' fs fs' κ).app K ≫ fs'.map ψ)) ≫
      eG.hom.app (fs'.obj L) ≫ rg.map (eF'.hom.app L) =
    eF.hom.app K ≫ rf.map (ΓX.map (adj'.unit.app K ≫ gs'.map ψ) ≫ eG'.hom.app L) ≫
      σ.hom.app (ΓX'.obj L) := by
  have h := Stacks.Cohomology.BaseChange.unit_comp_map_mate adj adj' fs fs' κ K
  have hn := κ.hom.naturality ψ
  simp only [Functor.comp_map] at hn
  have hmate : adj.unit.app (fs.obj K) ≫
      gs.map ((Stacks.Cohomology.BaseChange.mate adj adj' fs fs' κ).app K ≫ fs'.map ψ) =
        fs.map (adj'.unit.app K ≫ gs'.map ψ) ≫ κ.hom.app L := by
    rw [Functor.map_comp, reassoc_of% h, ← hn, Functor.map_comp, Category.assoc]
  have he := eF.hom.naturality (adj'.unit.app K ≫ gs'.map ψ)
  simp only [Functor.comp_map] at he
  rw [hmate, Functor.map_comp, Category.assoc, hD0, reassoc_of% he]
  simp only [Functor.map_comp, Category.assoc]

section Homology

variable {c : ComplexShape ℕ}
  [fs.Additive] [gs.Additive] [fs'.Additive] [gs'.Additive] [gu.Additive] [gu'.Additive]
  [ΓY.Additive] [ΓY'.Additive] [ΓX.Additive] [ΓX'.Additive] [rf.Additive] [rg.Additive]
  [rg'.Additive] [rf'.Additive]

omit [Abelian MX] [Abelian MY] [Abelian MX'] [Abelian EA] [Abelian EA'] [Abelian EX]
  [Abelian EX'] in
/-- The base change map on complexes: the degree-zero base change map (the mate of `κ`) on `I`,
followed by `f'_*ψ`. -/
def baseChangeComplexMap (I : HomologicalComplex MX c) {J : HomologicalComplex MX' c}
    (ψ : (gu'.mapHomologicalComplex c).obj I ⟶ J) :
    (gu.mapHomologicalComplex c).obj ((fs.mapHomologicalComplex c).obj I) ⟶
      (fs'.mapHomologicalComplex c).obj J :=
  (NatTrans.mapHomologicalComplex (Stacks.Cohomology.BaseChange.mate adj adj' fs fs' κ) c).app I ≫
    (fs'.mapHomologicalComplex c).map ψ

/-- **The chain identity.**  The degreewise square
`Stacks.Cohomology.RightDerivedCoEdge.baseChange_square_component` on complexes. -/
theorem baseChange_square_complex
    (hD0 : ∀ N : MX', ΓY.map (κ.hom.app N) ≫ eG.hom.app (fs'.obj N) ≫ rg.map (eF'.hom.app N) =
      eF.hom.app (gs'.obj N) ≫ rf.map (eG'.hom.app N) ≫ σ.hom.app (ΓX'.obj N))
    (I : HomologicalComplex MX c) {J : HomologicalComplex MX' c}
    (ψ : (gu'.mapHomologicalComplex c).obj I ⟶ J) :
    ((ΓY.mapHomologicalComplex c).map
        (unitHomologicalComplex adj ((fs.mapHomologicalComplex c).obj I) ≫
          (gs.mapHomologicalComplex c).map
            ((NatTrans.mapHomologicalComplex (Stacks.Cohomology.BaseChange.mate adj adj' fs fs' κ)
              c).app I ≫ (fs'.mapHomologicalComplex c).map ψ)) ≫
        (NatTrans.mapHomologicalComplex eG.hom c).app ((fs'.mapHomologicalComplex c).obj J)) ≫
      (rg.mapHomologicalComplex c).map ((NatIso.mapHomologicalComplex eF' c).app J).hom =
    ((NatIso.mapHomologicalComplex eF c).app I).hom ≫
      (rf.mapHomologicalComplex c).map ((ΓX.mapHomologicalComplex c).map
        (unitHomologicalComplex adj' I ≫ (gs'.mapHomologicalComplex c).map ψ) ≫
          (NatTrans.mapHomologicalComplex eG'.hom c).app J) ≫
      (NatTrans.mapHomologicalComplex σ.hom c).app ((ΓX'.mapHomologicalComplex c).obj J) := by
  ext k
  have h := baseChange_square_component adj adj' κ eF eG eF' eG' σ hD0 (I.X k) (ψ.f k)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f] at h ⊢
  simp only [unitHomologicalComplex, Category.assoc, Functor.map_comp] at h ⊢
  exact h

/-- **The base change map on cohomology, transposed and read on global sections.**

Let `I` be a complex on `X`, `J` one on `X'`, `ψ : (g')^*I ⟶ J`, and let
`Q : g^*f_*I ⟶ f'_*J` be the degree-zero base change map on `I` followed by `f'_*ψ`.  In degree
`n`, the morphism `θ : g^*Hⁿ(f_*I) ⟶ Hⁿ(f'_*J)` that `Q` induces, transposed across `g^* ⊣ g_*`
and read on global sections of `Y` and `Y'`, is identified — through isomorphisms on both sides
— with a morphism `p₀ : R ⟶ r_{g'}(R')` that computes, on cohomology of the complexes of global
sections, the pullback along `γ = (unit) ≫ g'_*ψ : I ⟶ g'_*J` followed by **Stacks 0732** for
`g'`, read through `σ`. -/
theorem baseChange_homology_globalSections
    [PreservesFiniteLimits gu] [PreservesFiniteColimits gu] [PreservesFiniteLimits gs]
    [PreservesFiniteLimits ΓY] [PreservesFiniteLimits ΓY'] [PreservesFiniteLimits ΓX]
    [PreservesFiniteLimits ΓX'] [PreservesFiniteLimits rg] [PreservesFiniteLimits rf]
    [PreservesFiniteLimits rg'] [PreservesFiniteLimits rf'] [PreservesFiniteColimits rf']
    (hD0 : ∀ N : MX', ΓY.map (κ.hom.app N) ≫ eG.hom.app (fs'.obj N) ≫ rg.map (eF'.hom.app N) =
      eF.hom.app (gs'.obj N) ≫ rf.map (eG'.hom.app N) ≫ σ.hom.app (ΓX'.obj N))
    (I : HomologicalComplex MX c) {J : HomologicalComplex MX' c}
    (ψ : (gu'.mapHomologicalComplex c).obj I ⟶ J) (n : ℕ) {RX : EX} {RX' : EX'}
    (iX : RX ≅ ((ΓX.mapHomologicalComplex c).obj I).homology n)
    (jX : RX' ≅ ((ΓX'.mapHomologicalComplex c).obj J).homology n) (p₀ : RX ⟶ rg'.obj RX')
    (hp : iX.inv ≫ p₀ = HomologicalComplex.homologyMap ((ΓX.mapHomologicalComplex c).map
        (unitHomologicalComplex adj' I ≫ (gs'.mapHomologicalComplex c).map ψ) ≫
          (NatTrans.mapHomologicalComplex eG'.hom c).app J) n ≫
        homologyToMapHomology rg' ((ΓX'.mapHomologicalComplex c).obj J) n ≫ rg'.map jX.inv) :
    homologyToMapHomology ΓY ((fs.mapHomologicalComplex c).obj I) n ≫
        ΓY.map (adj.unit.app (((fs.mapHomologicalComplex c).obj I).homology n)) ≫
        eG.hom.app (gu.obj (((fs.mapHomologicalComplex c).obj I).homology n)) ≫
        rg.map (ΓY'.map (inv (homologyToMapHomology gu ((fs.mapHomologicalComplex c).obj I) n) ≫
          HomologicalComplex.homologyMap (baseChangeComplexMap adj adj' κ I ψ) n)) =
      (HomologicalComplex.homologyMap ((NatIso.mapHomologicalComplex eF c).app I).hom n ≫
          homologyToMapHomology rf ((ΓX.mapHomologicalComplex c).obj I) n ≫ rf.map iX.inv) ≫
        (rf.map p₀ ≫ σ.hom.app RX') ≫
        rg.map (rf'.map jX.hom ≫
          inv (homologyToMapHomology rf' ((ΓX'.mapHomologicalComplex c).obj J) n) ≫
          HomologicalComplex.homologyMap ((NatIso.mapHomologicalComplex eF' c).app J).inv n ≫
          homologyToMapHomology ΓY' ((fs'.mapHomologicalComplex c).obj J) n) := by
  have L := homologyToMapHomology_comp_unit_comp_natIso_comp_map adj ΓY ΓY' rg eG
    ((fs.mapHomologicalComplex c).obj I) ((fs'.mapHomologicalComplex c).obj J)
    ((NatTrans.mapHomologicalComplex (Stacks.Cohomology.BaseChange.mate adj adj' fs fs' κ)
      c).app I ≫ (fs'.mapHomologicalComplex c).map ψ) n
  have Sq := homologyMap_comp_homologyToMapHomology_of_square σ
    (C₁ := (ΓY.mapHomologicalComplex c).obj ((fs.mapHomologicalComplex c).obj I))
    (C₂ := (ΓX.mapHomologicalComplex c).obj I)
    (D₁ := (ΓY'.mapHomologicalComplex c).obj ((fs'.mapHomologicalComplex c).obj J))
    (D₂ := (ΓX'.mapHomologicalComplex c).obj J)
    ((NatIso.mapHomologicalComplex eF c).app I) ((NatIso.mapHomologicalComplex eF' c).app J)
    ((ΓX.mapHomologicalComplex c).map
      (unitHomologicalComplex adj' I ≫ (gs'.mapHomologicalComplex c).map ψ) ≫
        (NatTrans.mapHomologicalComplex eG'.hom c).app J)
    _ (baseChange_square_complex adj adj' κ eF eG eF' eG' σ hD0 I ψ) n iX jX p₀ hp
  rw [baseChangeComplexMap, L, ← Category.assoc, ← Category.assoc,
    ← HomologicalComplex.homologyMap_comp, Sq]
  simp only [Functor.map_comp, Category.assoc]

end Homology

/-- **Invertibility read through transposes.**  For an adjunction `L ⊣ R`, if
`u ≫ R(θ) = x ≫ p ≫ R(y)` with `x` and `y` invertible and the transposes of `u` and `p`
invertible, then `θ` is invertible. -/
theorem isIso_of_transpose_eq {A B : Type*} [Category* A] [Category* B] {L : A ⥤ B} {R : B ⥤ A}
    (adj : L ⊣ R) {M N : A} {P P' Q : B} (u : M ⟶ R.obj P) (θ : P ⟶ P') (x : M ⟶ N)
    (p : N ⟶ R.obj Q) (y : Q ⟶ P') [IsIso ((adj.homEquiv _ _).symm u)] [IsIso x]
    [IsIso ((adj.homEquiv _ _).symm p)] [IsIso y] (h : u ≫ R.map θ = x ≫ p ≫ R.map y) :
    IsIso θ := by
  have h' := congrArg (adj.homEquiv _ _).symm h
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm] at h'
  have : IsIso ((adj.homEquiv _ _).symm u ≫ θ) := by
    rw [h']
    infer_instance
  exact IsIso.of_isIso_comp_left ((adj.homEquiv _ _).symm u) θ

/-- `Stacks.Cohomology.RightDerivedCoEdge.isIso_of_transpose_eq` with an invertible morphism
precomposed on the left and the transposed morphism written as a composite. -/
theorem isIso_of_comp_transpose_eq {A B : Type*} [Category* A] [Category* B] {L : A ⥤ B}
    {R : B ⥤ A} (adj : L ⊣ R) {M₀ M M' N : A} {P P' Q : B} (E : M₀ ⟶ M) (a : M ⟶ M')
    (b : M' ⟶ R.obj P) (θ : P ⟶ P') (e : M₀ ⟶ N) (p : N ⟶ R.obj Q) (y : Q ⟶ P') [IsIso E]
    [IsIso ((adj.homEquiv _ _).symm (a ≫ b))] [IsIso e] [IsIso ((adj.homEquiv _ _).symm p)]
    [IsIso y] (h : E ≫ a ≫ b ≫ R.map θ = e ≫ p ≫ R.map y) : IsIso θ :=
  isIso_of_transpose_eq adj (a ≫ b) θ (inv E ≫ e) p y (by
    rw [← cancel_epi E]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using h)

/-- `Stacks.Cohomology.RightDerivedCoEdge.isIso_of_comp_transpose_eq`, with the composite whose
transpose is invertible named. -/
theorem isIso_of_comp_transpose_eq_of_eq {A B : Type*} [Category* A] [Category* B] {L : A ⥤ B}
    {R : B ⥤ A} (adj : L ⊣ R) {M₀ M M' N : A} {P P' Q : B} (E : M₀ ⟶ M) (a : M ⟶ M')
    (b : M' ⟶ R.obj P) (v : M ⟶ R.obj P) (hv : a ≫ b = v) (θ : P ⟶ P') (e : M₀ ⟶ N)
    (p p' : N ⟶ R.obj Q) (hp : p = p') (y : Q ⟶ P') (hE : IsIso E)
    (hv' : IsIso ((adj.homEquiv _ _).symm v)) (he : IsIso e)
    (hp' : IsIso ((adj.homEquiv _ _).symm p')) (hy : IsIso y)
    (h : E ≫ a ≫ b ≫ R.map θ = e ≫ p ≫ R.map y) : IsIso θ := by
  subst hv hp
  exact isIso_of_comp_transpose_eq adj E a b θ e p y h

section Homology'

variable {c : ComplexShape ℕ}
  [fs.Additive] [gs.Additive] [fs'.Additive] [gs'.Additive] [gu.Additive] [gu'.Additive]
  [ΓY.Additive] [ΓY'.Additive] [ΓX.Additive] [ΓX'.Additive] [rf.Additive] [rg.Additive]
  [rg'.Additive] [rf'.Additive]

/-- **The base change map on cohomology is invertible on global sections**, as soon as the
transposes of the inverse image of global sections and of the pullback map `p'` are: this is
`Stacks.Cohomology.RightDerivedCoEdge.baseChange_homology_globalSections` read through
`Stacks.Cohomology.RightDerivedCoEdge.isIso_of_comp_transpose_eq_of_eq`. -/
theorem isIso_globalSections_baseChange_homology
    [PreservesFiniteLimits gu] [PreservesFiniteColimits gu] [PreservesFiniteLimits gs]
    [PreservesFiniteLimits ΓY] [PreservesFiniteLimits ΓY'] [PreservesFiniteLimits ΓX]
    [PreservesFiniteLimits ΓX'] [PreservesFiniteLimits rg] [PreservesFiniteLimits rf]
    [PreservesFiniteColimits rf] [PreservesFiniteLimits rg'] [PreservesFiniteLimits rf']
    [PreservesFiniteColimits rf']
    (hD0 : ∀ N : MX', ΓY.map (κ.hom.app N) ≫ eG.hom.app (fs'.obj N) ≫ rg.map (eF'.hom.app N) =
      eF.hom.app (gs'.obj N) ≫ rf.map (eG'.hom.app N) ≫ σ.hom.app (ΓX'.obj N))
    (I : HomologicalComplex MX c) {J : HomologicalComplex MX' c}
    (ψ : (gu'.mapHomologicalComplex c).obj I ⟶ J) (n : ℕ) {RX : EX} {RX' : EX'}
    (iX : RX ≅ ((ΓX.mapHomologicalComplex c).obj I).homology n)
    (jX : RX' ≅ ((ΓX'.mapHomologicalComplex c).obj J).homology n) (p₀ : RX ⟶ rg'.obj RX')
    (hp : iX.inv ≫ p₀ = HomologicalComplex.homologyMap ((ΓX.mapHomologicalComplex c).map
        (unitHomologicalComplex adj' I ≫ (gs'.mapHomologicalComplex c).map ψ) ≫
          (NatTrans.mapHomologicalComplex eG'.hom c).app J) n ≫
        homologyToMapHomology rg' ((ΓX'.mapHomologicalComplex c).obj J) n ≫ rg'.map jX.inv)
    {Lx : EA ⥤ EA'} (adjE : Lx ⊣ rg)
    (v : ΓY.obj (((fs.mapHomologicalComplex c).obj I).homology n) ⟶
      rg.obj (ΓY'.obj (gu.obj (((fs.mapHomologicalComplex c).obj I).homology n))))
    (hv : ΓY.map (adj.unit.app (((fs.mapHomologicalComplex c).obj I).homology n)) ≫
      eG.hom.app (gu.obj (((fs.mapHomologicalComplex c).obj I).homology n)) = v)
    (hv' : IsIso ((adjE.homEquiv _ _).symm v)) (p' : rf.obj RX ⟶ rg.obj (rf'.obj RX'))
    (hpp : rf.map p₀ ≫ σ.hom.app RX' = p') (hp' : IsIso ((adjE.homEquiv _ _).symm p'))
    (hE : IsIso (homologyToMapHomology ΓY ((fs.mapHomologicalComplex c).obj I) n))
    (hE' : IsIso (homologyToMapHomology ΓY' ((fs'.mapHomologicalComplex c).obj J) n)) :
    IsIso (ΓY'.map (inv (homologyToMapHomology gu ((fs.mapHomologicalComplex c).obj I) n) ≫
      HomologicalComplex.homologyMap (baseChangeComplexMap adj adj' κ I ψ) n)) :=
  isIso_of_comp_transpose_eq_of_eq adjE _ _ _ v hv _ _ _ p' hpp _ hE hv' inferInstance hp'
    inferInstance
    (baseChange_homology_globalSections adj adj' κ eF eG eF' eG' σ hD0 I ψ n iX jX p₀ hp)

end Homology'

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (τ : F ⋙ G ⟶ G' ⋙ F')
  (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)
  {P : D ⥤ B} {P' : C ⥤ A} {Fm : A ⥤ B} {F'm : C ⥤ D}
  [Fm.Additive] [F'm.Additive]

/-- **The descended base change comparison at `X[0]`, from the base change map on complexes of a
transported square.**  Let `τ : F ⋙ G ⟶ G' ⋙ F'` be the base change mate of a comparison
`κ : P' ⋙ Fm ≅ F'm ⋙ P` across adjunctions `G ⊣ P` and `G' ⊣ P'`, read through isomorphisms
`α : F ≅ Fm` and `β : F' ≅ F'm`.  If the base change map on complexes
`Stacks.Cohomology.RightDerivedCoEdge.baseChangeComplexMap` at the chosen injective resolution of
`X` and a quasi-isomorphism `ψ : G'(I) ⟶ J` onto an injective resolution of `G'(X)` is a
quasi-isomorphism, then the descended comparison is invertible at `X` placed in degree zero. -/
theorem isIso_derived_app_single_of_quasiIso_baseChangeComplexMap (adj : G ⊣ P) (adj' : G' ⊣ P')
    (κ : P' ⋙ Fm ≅ F'm ⋙ P) (α : F ≅ Fm) (β : F' ≅ F'm)
    (hτ : τ = Functor.whiskerRight α.hom G ≫
      Stacks.Cohomology.BaseChange.mate adj adj' Fm F'm κ ≫ Functor.whiskerLeft G' β.inv)
    (X : A) {Z : C} (J : InjectiveResolution Z)
    (ψ : (G'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution X).cocomplex ⟶ J.cocomplex) [QuasiIso ψ]
    (h : QuasiIso (baseChangeComplexMap adj adj' κ (injectiveResolution X).cocomplex ψ)) :
    IsIso ((Stacks.Cohomology.BaseChange.derived F F' G G' τ e).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj X)) :=
  Stacks.Cohomology.BaseChange.isIso_derived_app_single_of_quasiIso_cocomplex F F' G G' τ e X J ψ
    (Stacks.Cohomology.BaseChange.quasiIso_comp_mapHomologicalComplex_of_eq_whisker F F' G G' τ
      α β _ hτ _ ψ h)

end Derived

end Stacks.Cohomology.RightDerivedCoEdge

end
