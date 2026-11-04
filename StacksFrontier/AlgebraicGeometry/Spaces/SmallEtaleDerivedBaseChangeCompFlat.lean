module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuadrupleEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineSectionsFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompCondition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeAffineModel

/-!
# Stacks 0A1K: base change for a bounded above complex flat over the base

Let `g' ≫ f = f' ≫ g` be a cartesian square of algebraic spaces with `f` quasi-compact and
quasi-separated, and let `𝒢^•` be a bounded above complex of quasi-coherent `𝒪_X`-modules flat
over `Y`. Then the composite

`Lg^*Rf_*𝒢^• ⟶ Rf'_*L(g')^*𝒢^• ⟶ Rf'_*(g')^*𝒢^•`

of the base change map with the comparison of the derived with the degreewise pullback is an
isomorphism. The proof is the source's: condition (2) of Stacks 0DKG holds for the comparison,
because on an affine étale quadruple the sections of `𝒢^•` form a bounded above complex of
modules flat over the base ring, for which the comparison of Stacks 065Z is computed termwise.

## Main results

* `AlgebraicGeometry.Space.affineChartwiseBaseChange_pullbackQComparison`: condition (2) of
  Stacks 0DKG for the comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•`.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_pullbackQComparison`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CategoryTheory.BaseChange

/-- Naturality of a composite `L(a) ≫ c ≫ d` of three natural families. -/
theorem map_comp_eq_of_three {D D' : Type*} [Category* D] [Category* D'] (L : D ⥤ D')
    {A₁ A₂ B₁ B₂ : D} {C₁ C₂ E₁ E₂ : D'} (x : A₁ ⟶ A₂) (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂)
    (y : B₁ ⟶ B₂) (c₁ : L.obj B₁ ⟶ C₁) (c₂ : L.obj B₂ ⟶ C₂) (z : C₁ ⟶ C₂) (d₁ : C₁ ⟶ E₁)
    (d₂ : C₂ ⟶ E₂) (t : E₁ ⟶ E₂) (h₁ : x ≫ a₂ = a₁ ≫ y) (h₂ : L.map y ≫ c₂ = c₁ ≫ z)
    (h₃ : z ≫ d₂ = d₁ ≫ t) {φ₁ : L.obj A₁ ⟶ E₁} {φ₂ : L.obj A₂ ⟶ E₂}
    (hφ₂ : φ₂ = L.map a₂ ≫ c₂ ≫ d₂) (hφ₁ : φ₁ = L.map a₁ ≫ c₁ ≫ d₁) :
    L.map x ≫ φ₂ = φ₁ ≫ t := by
  subst hφ₁ hφ₂
  rw [← L.map_comp_assoc, h₁, L.map_comp_assoc, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

/-- Bookkeeping for the restriction of the comparison of derived with degreewise pullbacks to an
affine étale quadruple: the two composition laws and the transport along `g₀' ≫ a = a' ≫ g'`. -/
theorem comp_eq_of_comparisons {D : Type*} [Category* D] {A B C E A₁ A₂ E' A₃ F F' : D}
    (x : A ⟶ B) (y : B ⟶ C) (z : C ⟶ E) (z' : E ⟶ C) (hz : z ≫ z' = 𝟙 C) (i₁ : A ⟶ A₁)
    (p : A₁ ⟶ E) (h₁ : x ≫ y ≫ z = i₁ ≫ p) (cg : A₁ ⟶ A₂) (p' : A₂ ⟶ E') (t : E ⟶ E')
    (t' : E' ⟶ E) (ht : t ≫ t' = 𝟙 E) (h₃ : cg ≫ p' = p ≫ t) (j : A₃ ≅ A₂) (m : A₃ ⟶ F)
    (n : F ⟶ F') (k : F' ⟶ E') (h₂ : m ≫ n ≫ k = j.hom ≫ p') :
    x ≫ y = (i₁ ≫ cg ≫ j.inv ≫ m) ≫ n ≫ k ≫ t' ≫ z' := by
  simp only [Category.assoc]
  rw [reassoc_of% h₂, Iso.inv_hom_id_assoc, reassoc_of% h₃, reassoc_of% ht, ← reassoc_of% h₁,
    hz, Category.comp_id]

end Stacks.CategoryTheory.BaseChange

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] additive_extendScalars_representedAffineRingHom
  additive_pullbackModules_representedSpaceMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comparison

variable {X X' : AlgebraicSpaces B S hS}

section Naturality

attribute [local instance 6000] preadditive_smallEtaleModules

/-- **The comparison of the derived with the degreewise pullback is natural** in the complex. -/
theorem smallEtaleDerivedPullbackQComparison_naturality (g : X' ⟶ X)
    {G₁ G₂ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ}
    (v : G₁ ⟶ G₂) :
    (smallEtaleDerivedModulePullback B S hS g).map (DerivedCategory.Q.map v) ≫
        smallEtaleDerivedPullbackQComparison g G₂ =
      smallEtaleDerivedPullbackQComparison g G₁ ≫
        DerivedCategory.Q.map (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS g).toModulesHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map v) := by
  let P := (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS g).toModulesHom).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let qX := DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  let qX' := DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))
  let c := smallEtaleDerivedModulePullbackComparison B S hS g
  let hv := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map v
  have h₁ : DerivedCategory.Q.map v ≫ qX.inv.app G₂ = qX.inv.app G₁ ≫ DerivedCategory.Qh.map hv :=
    qX.inv.naturality v
  have h₂ : (smallEtaleDerivedModulePullback B S hS g).map (DerivedCategory.Qh.map hv) ≫
      c.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj G₂) =
      c.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj G₁) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (P.map v)) :=
    c.naturality hv
  have h₃ : DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (P.map v)) ≫ qX'.hom.app (P.obj G₂) =
        qX'.hom.app (P.obj G₁) ≫ DerivedCategory.Q.map (P.map v) :=
    qX'.hom.naturality (P.map v)
  exact Stacks.CategoryTheory.BaseChange.map_comp_eq_of_three
    (smallEtaleDerivedModulePullback B S hS g) _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃
    (smallEtaleDerivedPullbackQComparison.eq_1 _ _) (smallEtaleDerivedPullbackQComparison.eq_1 _ _)

end Naturality

/-- The transport of degreewise pullbacks of a complex along an equality of morphisms, in the
derived category. -/
def smallEtalePullbackCongrQIso {g₁ g₂ : X' ⟶ X} (h : g₁ = g₂)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    DerivedCategory.Q.obj (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS g₁).toModulesHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G) ≅
      DerivedCategory.Q.obj (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS g₂).toModulesHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G) :=
  DerivedCategory.Q.mapIso (eqToIso (congrArg (fun k : X' ⟶ X =>
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS k).toModulesHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj G) h))

/-- The transport along `h` followed by the transport along `h.symm` is the identity. -/
theorem smallEtalePullbackCongrQIso_hom_hom_symm {g₁ g₂ : X' ⟶ X} (h : g₁ = g₂)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (smallEtalePullbackCongrQIso B S hS h G).hom ≫
      (smallEtalePullbackCongrQIso B S hS h.symm G).hom = 𝟙 _ := by
  subst h
  simp [smallEtalePullbackCongrQIso]

/-- **The comparison of the derived with the degreewise pullback is compatible with the
transport along an equality of morphisms.** -/
theorem smallEtaleDerivedPullbackQComparison_congr {g₁ g₂ : X' ⟶ X} (h : g₁ = g₂)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (smallEtaleDerivedModulePullbackCongr B S hS h).hom.app (DerivedCategory.Q.obj G) ≫
        smallEtaleDerivedPullbackQComparison g₂ G =
      smallEtaleDerivedPullbackQComparison g₁ G ≫ (smallEtalePullbackCongrQIso B S hS h G).hom := by
  subst h
  simp [smallEtaleDerivedModulePullbackCongr, smallEtalePullbackCongrQIso]

section Comp

variable {X'' : AlgebraicSpaces B S hS}

/-- `AlgebraicGeometry.Space.smallEtaleDerivedPullbackQComparison_comp` with the composition law
of degreewise pullbacks abstracted as an isomorphism. -/
theorem exists_isIso_smallEtaleDerivedPullbackQComparison_comp (h : X'' ⟶ X') (g : X' ⟶ X)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    ∃ k : DerivedCategory.Q.obj (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X'') (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS h).toModulesHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS g).toModulesHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G)) ⟶
      DerivedCategory.Q.obj (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS X'') (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS (h ≫ g)).toModulesHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G),
      IsIso k ∧
      (smallEtaleDerivedModulePullback B S hS h).map (smallEtaleDerivedPullbackQComparison g G) ≫
          smallEtaleDerivedPullbackQComparison h
            (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
                (smallEtaleRingedToposHom B S hS g).toModulesHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G) ≫ k =
        (smallEtaleDerivedModulePullbackCompIso B S hS h g).hom.app (DerivedCategory.Q.obj G) ≫
          smallEtaleDerivedPullbackQComparison (h ≫ g) G :=
  ⟨_, Functor.map_isIso _ _, smallEtaleDerivedPullbackQComparison_comp B S hS h g G⟩

end Comp

/-- Along an étale morphism the comparison of the derived with the degreewise pullback is an
isomorphism. -/
theorem isIso_smallEtaleDerivedPullbackQComparison_of_isEtale (g : X' ⟶ X)
    (hg : IsEtale B S hS g.hom)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    IsIso (smallEtaleDerivedPullbackQComparison g G) := by
  have := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isEtale B S hS g hg
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj G)
  rw [smallEtaleDerivedPullbackQComparison.eq_1]
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) (IsIso.comp_isIso' inferInstance
    (Iso.isIso_hom ((DerivedCategory.quotientCompQhIso _).app _)))

end Comparison

section AffineSquare

variable {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U)

/-- **Stacks 0A1K for a cartesian square of affine representables.** For a bounded above complex
`𝒢^•` of quasi-coherent modules on `U` whose sections are flat over `Γ(V)`, the composite of
Stacks 0DKH at `𝒢^•` and the comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•` is an isomorphism. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_pullbackQComparison_of_quasicoherent
    (hpb : IsPullback g₀' f₀' f₀ g₀)
    (G₀ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) ℤ) (b : ℤ) [G₀.IsStrictlyLE b]
    (hq : ∀ n, (G₀.X n).IsQuasicoherentOnSite)
    (hN : ∀ n, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((ModuleCat.restrictScalars.{u} (representedAffineCommRingCatHom B S hS f₀).hom).obj
        ((representedAffineSections B S hS U).obj (G₀.X n)))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' hpb.w)
        (DerivedCategory.Q.obj G₀) _
        (smallEtaleDerivedPullbackQComparison (representedSpaceMap B S hS g₀') G₀)) := by
  let N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ :=
    ((representedAffineSections B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj G₀
  have : N.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn => (representedAffineSections B S hS U).map_isZero
      (G₀.isZero_of_isStrictlyLE b n hn)
  have hW := isIso_smallEtaleDerivedBaseChangeComp_pullbackQComparison_of_flat B S hS
    f₀ g₀ f₀' g₀' hpb N b hN
  let uh : ((representedAffineToposAssociated B S hS U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ G₀ :=
    (NatTrans.mapHomologicalComplex (representedAffineAssociatedAdjunction B S hS U).counit
      (ComplexShape.up ℤ)).app G₀
  have : ∀ n, IsIso (uh.f n) := fun n =>
    isIso_representedAffineAssociatedAdjunction_counit_app_tensor B S hS U (G₀.X n) (hq n)
  have : IsIso uh := HomologicalComplex.Hom.isIso_of_components uh
  exact (isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS _ _ _ _
    (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' hpb.w) _ _
    (smallEtaleDerivedPullbackQComparison (representedSpaceMap B S hS g₀')
      (((representedAffineToposAssociated B S hS U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N)) _ _
    (smallEtaleDerivedPullbackQComparison (representedSpaceMap B S hS g₀') G₀)
    (DerivedCategory.Q.mapIso (asIso uh))
    (DerivedCategory.Q.mapIso (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
      (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS g₀')).toModulesHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (asIso uh)))
    (smallEtaleDerivedPullbackQComparison_naturality B S hS _ uh)).1 hW

end AffineSquare

section Condition

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- Degreewise pullback of a quasi-coherent module along a morphism of algebraic spaces, in the
spelling of the morphism of small étale ringed topoi, is quasi-coherent. -/
theorem isQuasicoherentOnSite_pullbackModules (h : X' ⟶ X)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) :
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS h).toModulesHom).obj M).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((pullbackModulesIsoModulePullback B S hS h).app M).symm
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS h M hM)

/-- **Condition (2) of Stacks 0DKG for the comparison of the derived with the degreewise
pullback** of a bounded above complex of quasi-coherent modules flat over the base, for a
cartesian square. -/
theorem affineChartwiseBaseChange_pullbackQComparison (sq : IsPullback g' f' f g)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) (b : ℤ)
    [G.IsStrictlyLE b] (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) :
    AffineChartwiseBaseChange B S hS f g f' g' sq.w (DerivedCategory.Q.obj G) _
      (smallEtaleDerivedPullbackQComparison g' G) := by
  constructor
  intro U V V' U' _ _ _ _ a bV c a' f₀ g₀ f₀' g₀' w₀ ha hb hc hpb hfa hgb hfc ha'
  have hqG : QcohDerived B S hS X (DerivedCategory.Q.obj G) :=
    qcohDerived_Q_obj_of_isQuasicoherentOnSite G hq
  have hqG' : QcohDerived B S hS X' (DerivedCategory.Q.obj
      (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj G)) :=
    qcohDerived_Q_obj_of_isQuasicoherentOnSite _ fun n =>
      isQuasicoherentOnSite_pullbackModules B S hS g' (G.X n) (hq n)
  refine (isIso_smallEtaleDerivedBaseChangeComp_representedAffine_iff B S hS f₀ g₀ f₀' g₀' w₀ _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a _ hqG) _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' _ hqG') _).1 ?_
  have ha'e : IsEtale B S hS a'.hom :=
    isEtale_of_isPullback_of_etaleQuadruple B S hS sq ha hb hc
      (isPullback_representedSpaceMap B S hS hpb) hfa hgb hfc ha'
  have := pullbackModules_smallEtale_additive (B := B) (S := S) (hS := hS) a
  have := pullbackModules_smallEtale_additive (B := B) (S := S) (hS := hS) a'
  have := pullbackModules_smallEtale_additive (B := B) (S := S) (hS := hS) g'
  have := pullbackModules_smallEtale_additive (B := B) (S := S) (hS := hS)
    (representedSpaceMap B S hS g₀')
  -- the restriction of `𝒢` to `U`
  let G₀ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) ℤ :=
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS a).toModulesHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj G
  have : G₀.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn => (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS a).toModulesHom).map_isZero
      (G.isZero_of_isStrictlyLE b n hn)
  have hG₀q : ∀ n, (G₀.X n).IsQuasicoherentOnSite := fun n =>
    isQuasicoherentOnSite_pullbackModules B S hS a (G.X n) (hq n)
  have hG₀f : ∀ n, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((ModuleCat.restrictScalars.{u} (representedAffineCommRingCatHom B S hS f₀).hom).obj
        ((representedAffineSections B S hS U).obj (G₀.X n))) := fun n => by
    have h := flat_representedAffineSections_modulePullback_of_isFlatOver B S hS f (G.X n) (hq n)
      (hfl n) a ha bV hb f₀ hfa
    exact Module.Flat.of_linearEquiv
      ((ModuleCat.restrictScalars.{u} (representedAffineCommRingCatHom B S hS f₀).hom).mapIso
        ((representedAffineSections B S hS U).mapIso
          ((pullbackModulesIsoModulePullback B S hS a).app (G.X n)))).toLinearEquiv
  have hA := isIso_smallEtaleDerivedBaseChangeComp_pullbackQComparison_of_quasicoherent B S hS
    f₀ g₀ f₀' g₀' hpb G₀ b hG₀q hG₀f
  have := isIso_smallEtaleDerivedPullbackQComparison_of_isEtale B S hS a ha G
  have := isIso_smallEtaleDerivedPullbackQComparison_of_isEtale B S hS a' ha'e
    (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj G)
  refine (exists_isIso_smallEtaleDerivedPullbackQComparison_comp B S hS
    (representedSpaceMap B S hS g₀') a G).elim fun k₁ hk₁ => ?_
  refine (exists_isIso_smallEtaleDerivedPullbackQComparison_comp B S hS a' g' G).elim
    fun k₂ hk₂ => ?_
  have := hk₁.1
  have := hk₂.1
  refine (isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS _ _ _ _
    (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) _ _ _ _ _
    (smallEtaleDerivedPullbackQComparison (representedSpaceMap B S hS g₀') G₀)
    (asIso (smallEtaleDerivedPullbackQComparison a G))
    (asIso (smallEtaleDerivedPullbackQComparison a' _) ≪≫ asIso k₂ ≪≫
      smallEtalePullbackCongrQIso B S hS ha'.symm G ≪≫ (asIso k₁).symm) ?_).2 hA
  exact Stacks.CategoryTheory.BaseChange.comp_eq_of_comparisons _ _ _ _
    (IsIso.hom_inv_id k₁) _ _ hk₁.2 _ _ _ _ (smallEtalePullbackCongrQIso_hom_hom_symm B S hS ha' G)
    (smallEtaleDerivedPullbackQComparison_congr B S hS ha' G)
    ((smallEtaleDerivedModulePullbackCompIso B S hS a' g').app _) _ _ _ hk₂.2

end Condition

/-- The composite of Stacks 0DKH attached to `φ ≫ ψ` is invertible when the one attached to `φ`
is, for `ψ` invertible. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_comp_inv {X Y X' Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {K₁ K₂ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K₁) (ψ : K₁ ⟶ K₂)
    (h : IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K₁ φ)) (hψ : IsIso ψ) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K₂ (φ ≫ ψ)) := by
  rw [← smallEtaleDerivedBaseChangeComp_comp]
  exact IsIso.comp_isIso' h (Functor.map_isIso _ ψ)

section Main

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- **Stacks 0A1K for a bounded above complex.** For a cartesian square of algebraic spaces with
`f` quasi-compact and quasi-separated and a bounded above complex `𝒢^•` of quasi-coherent
`𝒪_X`-modules flat over `Y`, the composite `Lg^*Rf_*𝒢^• ⟶ Rf'_*L(g')^*𝒢^• ⟶ Rf'_*(g')^*𝒢^•` of
the base change map with the comparison of the derived with the degreewise pullback is an
isomorphism. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_pullbackQComparison_of_isFlatOver
    (sq : IsPullback g' f' f g) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w (DerivedCategory.Q.obj G) _
      (smallEtaleDerivedPullbackQComparison g' G)) := by
  obtain ⟨b, hb⟩ := hGb
  have : G.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff G b).2 hb
  have := pullbackModules_smallEtale_additive (B := B) (S := S) (hS := hS) g'
  exact isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange B S hS sq hfqc hfqs
    _ (qcohDerived_Q_obj_of_isQuasicoherentOnSite G hq) _
    (qcohDerived_Q_obj_of_isQuasicoherentOnSite _ fun n =>
      isQuasicoherentOnSite_pullbackModules B S hS g' (G.X n) (hq n)) _
    (affineChartwiseBaseChange_pullbackQComparison B S hS sq G b hq hfl)

/-- **Stacks 0A1K for a bounded above complex**, with the degreewise pullback spelled as
`AlgebraicGeometry.Space.modulePullback`: the composite
`Lg^*Rf_*𝒢^• ⟶ Rf'_*L(g')^*𝒢^• ⟶ Rf'_*(g')^*𝒢^•` is an isomorphism. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_modulePullbackQComparison_of_isFlatOver
    (sq : IsPullback g' f' f g) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w (DerivedCategory.Q.obj G) _
      (smallEtaleDerivedModulePullbackQComparison g' G)) := by
  have h := isIso_smallEtaleDerivedBaseChangeComp_pullbackQComparison_of_isFlatOver B S hS sq hfqc
    hfqs G hGb hq hfl
  unfold smallEtaleDerivedModulePullbackQComparison
  exact isIso_smallEtaleDerivedBaseChangeComp_of_comp_inv B S hS f g f' g' sq.w _ _ _ h
    (@Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Q _ (NatIso.hom_app_isIso _ _))

end Main

end AlgebraicGeometry.Space
