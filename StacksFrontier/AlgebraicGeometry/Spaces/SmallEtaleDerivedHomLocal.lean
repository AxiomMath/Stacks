module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedAbove
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexUniqueness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackCompAssoc
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomBoundedBelow

/-!
# Local behaviour of the derived internal Hom of an algebraic space

Bounds on `R𝓗om(K, L)` on the small étale site of an algebraic space: they pass to every space
étale over it. When `R𝓗om(K, L)` lies in `D^{≥ 0}`, a morphism `K ⟶ L` is determined by its
derived pullbacks to a covering family of étale charts.

## Main results

* `AlgebraicGeometry.Space.isGE_smallEtaleDerivedSheafHom_pullback_of_isEtale`: derived pullback
  along an étale morphism preserves lower bounds of `R𝓗om(K, L)`.
* `AlgebraicGeometry.Space.eq_of_smallEtaleDerivedModulePullback_map_eq`: when `R𝓗om(K, L)` lies in
  `D^{≥ 0}`, two morphisms `K ⟶ L` with the same derived pullbacks to a covering family of
  charts are equal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  isGrothendieckAbelian_ringedToposStructureRingSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Derived pullback along an étale morphism preserves lower bounds of `R𝓗om`.** If
`R𝓗om(K, L)` lies in `D^{≥ n}` on `X` and `u : Z ⟶ X` is étale, then `R𝓗om(Lu^*K, Lu^*L)` lies
in `D^{≥ n}` on `Z`: on a chart `E` of `Z` both are `R𝓗om` restricted to the chart `E` of `X`. -/
theorem isGE_smallEtaleDerivedSheafHom_pullback_of_isEtale {Z X : AlgebraicSpaces B S hS}
    (u : Z ⟶ X) (hu : IsEtale B S hS u.hom)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (n : ℤ)
    (h : (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj L).IsGE n) :
    (((smallEtaleDerivedSheafHom B S hS Z).obj
      (op ((smallEtaleDerivedModulePullback B S hS u).obj K))).obj
        ((smallEtaleDerivedModulePullback B S hS u).obj L)).IsGE n := by
  refine isGE_of_isGE_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_affineCharts B S hS Z.1) _ n fun E => ?_
  let E' := (smallEtalePostcomp B S hS u hu).obj E.1
  have hE := isGE_smallEtaleDerivedModulePullback_obj_of_isEtale (chartToSpace B S hS X E')
    (isEtale_chartToSpace B S hS X E') _ n h
  let c := smallEtaleDerivedModulePullbackCompIso B S hS (chartToSpace B S hS Z E.1) u
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (smallEtaleDerivedSheafHomChartIso B S hS X E' K L ≪≫
      ((smallEtaleDerivedSheafHom B S hS (chartSpace B S hS Z E.1)).mapIso (c.app K).op).app _ ≪≫
      ((smallEtaleDerivedSheafHom B S hS (chartSpace B S hS Z E.1)).obj _).mapIso (c.app L).symm ≪≫
      (smallEtaleDerivedSheafHomChartIso B S hS Z E.1 _ _).symm) n

section Conj

variable {C : Type*} [Category* C]

/-- Conjugating by the two sides of a pasting of isomorphisms, in an arbitrary category. -/
theorem conj_conj_aux {P₁ P₂ Q₁ Q₂ R₁ R₂ T₁ T₂ : C} (a₁ : P₁ ≅ Q₁) (b₁ : Q₁ ≅ T₁)
    (x₁ : P₁ ≅ R₁) (y₁ : R₁ ≅ T₁) (h₁ : a₁.hom ≫ b₁.hom = x₁.hom ≫ y₁.hom) (a₂ : P₂ ≅ Q₂)
    (b₂ : Q₂ ≅ T₂) (x₂ : P₂ ≅ R₂) (y₂ : R₂ ≅ T₂) (h₂ : a₂.hom ≫ b₂.hom = x₂.hom ≫ y₂.hom)
    {φ₀ : P₁ ⟶ P₂} {φ₁ : Q₁ ⟶ Q₂} (hn : φ₀ ≫ a₂.hom = a₁.hom ≫ φ₁) {z : R₁ ⟶ R₂}
    (hz : z = x₁.inv ≫ φ₀ ≫ x₂.hom) :
    y₁.inv ≫ z ≫ y₂.hom = b₁.inv ≫ φ₁ ≫ b₂.hom := by
  have e₁ : y₁.inv ≫ x₁.inv = b₁.inv ≫ a₁.inv := by
    rw [← Iso.trans_inv, ← Iso.trans_inv]
    congr 1
    exact Iso.ext h₁.symm
  have e₂ : x₂.hom ≫ y₂.hom = a₂.hom ≫ b₂.hom := h₂.symm
  rw [hz]
  simp only [Category.assoc]
  rw [e₂, reassoc_of% hn, reassoc_of% e₁, Iso.inv_hom_id_assoc]

/-- Inserting identities around a conjugate, in an arbitrary category. -/
theorem eq_id_comp_comp_id_aux {P Q R T : C} {x : P ⟶ T} {a : P ⟶ Q} {φ : Q ⟶ R} {b : R ⟶ T}
    (h : x = a ≫ φ ≫ b) : x = (𝟙 P ≫ a) ≫ φ ≫ b ≫ 𝟙 T := by
  simpa using h

/-- Conjugation by isomorphisms is injective. -/
theorem eq_of_conj_eq {P P' Q Q' : C} (e₁ : P ≅ P') (e₂ : Q ≅ Q') {x y : P ⟶ Q}
    (h : e₁.inv ≫ x ≫ e₂.hom = e₁.inv ≫ y ≫ e₂.hom) : x = y := by
  simpa using h

end Conj

variable {B S hS}

/-- Derived pullback of a pulled back morphism is the derived pullback along the composite,
read through Stacks 0D6D and an equality `r ≫ u = u'`. -/
theorem compIso_congr_conj_map {Z' Z X : AlgebraicSpaces B S hS} (r : Z' ⟶ Z) (u : Z ⟶ X)
    {u' : Z' ⟶ X} (hr : r ≫ u = u')
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (d : K ⟶ L) :
    (smallEtaleDerivedModulePullbackCompIso B S hS r u ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS hr).inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS r).map
          ((smallEtaleDerivedModulePullback B S hS u).map d) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS r u ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hr).hom.app L =
      (smallEtaleDerivedModulePullback B S hS u').map d := by
  rw [← cancel_epi ((smallEtaleDerivedModulePullbackCompIso B S hS r u ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS hr).hom.app K), Iso.hom_inv_id_app_assoc]
  exact (smallEtaleDerivedModulePullbackCompIso B S hS r u ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS hr).hom.naturality d

/-- If the derived pullback of `d` along `u` is invertible, so is its derived pullback along any
`u' = r ≫ u`. -/
theorem isIso_map_of_comp_eq {Z' Z X : AlgebraicSpaces B S hS} (r : Z' ⟶ Z) (u : Z ⟶ X)
    {u' : Z' ⟶ X} (hr : r ≫ u = u')
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (d : K ⟶ L) (h : IsIso ((smallEtaleDerivedModulePullback B S hS u).map d)) :
    IsIso ((smallEtaleDerivedModulePullback B S hS u').map d) := by
  rw [← compIso_congr_conj_map r u hr d]
  infer_instance

/-- A transport along a defining equality `p = p` of a derived pullback is the identity. -/
theorem smallEtaleDerivedModulePullbackCongr_eq_refl {Z X : AlgebraicSpaces B S hS}
    {p : Z ⟶ X} (h : p = p) :
    smallEtaleDerivedModulePullbackCongr B S hS h = Iso.refl _ := by
  simp [smallEtaleDerivedModulePullbackCongr]

/-- **Restricting a pulled back morphism further** (the cocycle identity of Stacks 0D6D): for
`ρ : Z ⟶ X'`, `g' : X' ⟶ X` and `r : Z' ⟶ Z`, derived pullback along `r` of the morphism
`Lρ^* φ` read on `L(ρ ≫ g')^*` is `L(r ≫ ρ)^* φ` read on `L((r ≫ ρ) ≫ g')^*`. -/
theorem compIso_congr_conj_conj {Z' Z X' X : AlgebraicSpaces B S hS} (r : Z' ⟶ Z) (ρ : Z ⟶ X')
    (g' : X' ⟶ X) {u : Z ⟶ X} (hρ : ρ ≫ g' = u) {u' : Z' ⟶ X} (hr : r ≫ u = u')
    (h : (r ≫ ρ) ≫ g' = u')
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g').obj L) :
    (smallEtaleDerivedModulePullbackCompIso B S hS r u ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS hr).inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS r).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS ρ g' ≪≫
              smallEtaleDerivedModulePullbackCongr B S hS hρ).inv.app K ≫
            (smallEtaleDerivedModulePullback B S hS ρ).map φ ≫
              (smallEtaleDerivedModulePullbackCompIso B S hS ρ g' ≪≫
                smallEtaleDerivedModulePullbackCongr B S hS hρ).hom.app L) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS r u ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hr).hom.app L =
      (smallEtaleDerivedModulePullbackCompIso B S hS (r ≫ ρ) g' ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS h).inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS (r ≫ ρ)).map φ ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS (r ≫ ρ) g' ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS h).hom.app L := by
  subst hρ h
  rw [smallEtaleDerivedModulePullbackCongr_eq_refl, smallEtaleDerivedModulePullbackCongr_eq_refl,
    Iso.trans_refl, Iso.trans_refl]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.refl_inv, Iso.refl_hom, NatTrans.comp_app,
    NatTrans.id_app]
  refine eq_id_comp_comp_id_aux ?_
  exact conj_conj_aux ((smallEtaleDerivedModulePullbackCompIso B S hS r ρ).app _)
    ((smallEtaleDerivedModulePullbackCompIso B S hS (r ≫ ρ) g').app K)
    ((smallEtaleDerivedModulePullback B S hS r).mapIso
      ((smallEtaleDerivedModulePullbackCompIso B S hS ρ g').app K))
    ((smallEtaleDerivedModulePullbackCompIso B S hS r (ρ ≫ g')).app K)
    (smallEtaleDerivedModulePullbackCompIso_assoc_app B S hS r ρ g' K)
    ((smallEtaleDerivedModulePullbackCompIso B S hS r ρ).app _)
    ((smallEtaleDerivedModulePullbackCompIso B S hS (r ≫ ρ) g').app L)
    ((smallEtaleDerivedModulePullback B S hS r).mapIso
      ((smallEtaleDerivedModulePullbackCompIso B S hS ρ g').app L))
    ((smallEtaleDerivedModulePullbackCompIso B S hS r (ρ ≫ g')).app L)
    (smallEtaleDerivedModulePullbackCompIso_assoc_app B S hS r ρ g' L)
    ((smallEtaleDerivedModulePullbackCompIso B S hS r ρ).hom.naturality φ)
    ((Functor.map_comp _ _ _).trans (whisker_eq _ (Functor.map_comp _ _ _)))

/-- The morphism `La^* φ` read on `L(a ≫ g')^* ≅ Lu^*` only depends on `a`. -/
theorem compIso_congr_conj_eq_of_eq {Z X' X : AlgebraicSpaces B S hS} {a a' : Z ⟶ X'}
    (e : a = a') (g' : X' ⟶ X) {u : Z ⟶ X} (h : a ≫ g' = u) (h' : a' ≫ g' = u)
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g').obj L) :
    (smallEtaleDerivedModulePullbackCompIso B S hS a g' ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS h).inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS a).map φ ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS a g' ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS h).hom.app L =
      (smallEtaleDerivedModulePullbackCompIso B S hS a' g' ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS h').inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS a').map φ ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS a' g' ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS h').hom.app L := by
  subst e h
  rw [smallEtaleDerivedModulePullbackCongr_eq_refl]

variable (B S hS)

/-- `chartDerivedPullbackIso c` is Stacks 0D6D followed by the transport along
`chartMap c ≫ chartToSpace A = chartToSpace C`. -/
theorem chartDerivedPullbackIso_eq {X : AlgebraicSpaces B S hS} {C A : SmallEtale B S hS X.1}
    (c : C ⟶ A) :
    chartDerivedPullbackIso B S hS c =
      smallEtaleDerivedModulePullbackCompIso B S hS (chartMap B S hS X c)
          (chartToSpace B S hS X A) ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS (chartMap_comp_chartToSpace B S hS X c) :=
  rfl

/-- Derived pullbacks of a morphism along charts are compatible along morphisms of charts. -/
theorem chartDerivedPullbackIso_conj_map {X : AlgebraicSpaces B S hS}
    {C A : SmallEtale B S hS X.1} (c : C ⟶ A)
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (d : K ⟶ L) :
    (chartDerivedPullbackIso B S hS c).inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS (chartMap B S hS X c)).map
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X A)).map d) ≫
          (chartDerivedPullbackIso B S hS c).hom.app L =
      (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X C)).map d := by
  rw [chartDerivedPullbackIso_eq]
  exact compIso_congr_conj_map _ _ (chartMap_comp_chartToSpace B S hS X c) d

/-- **Morphisms are determined on étale charts** when `R𝓗om(K, L)` lies in `D^{≥ 0}`: two
morphisms `K ⟶ L` with the same derived pullbacks to a covering family of charts are equal. -/
theorem eq_of_smallEtaleDerivedModulePullback_map_eq {X : AlgebraicSpaces B S hS}
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (hKL : (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj L).IsGE 0)
    {ι : Type*} {A : ι → SmallEtale B S hS X.1} (hA : (SmallEtale.topology B S hS X.1).CoversTop A)
    {d d' : K ⟶ L}
    (h : ∀ i, (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (A i))).map d =
      (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (A i))).map d') :
    d = d' := by
  obtain ⟨d₀, -, hu⟩ := existsUnique_smallEtaleDerivedModulePullback_map_eq B S hS hKL hA
    (fun i => (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (A i))).map d)
    (fun C i j c c' => by
      rw [chartDerivedPullbackIso_conj_map, chartDerivedPullbackIso_conj_map])
  exact (hu d fun _ => rfl).trans (hu d' fun i => (h i).symm).symm

end AlgebraicGeometry.Space

end
