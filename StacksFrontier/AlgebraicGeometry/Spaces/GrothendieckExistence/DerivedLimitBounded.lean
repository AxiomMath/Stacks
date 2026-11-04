module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatSheafSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedCoherator.Bound
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedLimitsCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree

/-!
# The derived limit of Situation 0CX4 is bounded, in degrees at least zero

In Situation [Stacks, Tag 0CX4] let `K = R lim_{D_QCoh(𝒪_X)}(Fₙ) = DQ_X(R lim_{D(𝒪_X)} Fₙ)`.
[Stacks, Tag 0CX5] says that `K` lies in `D^b_QCoh(𝒪_X)` and has nonzero cohomology sheaves only
in degrees `≥ 0`.

## Main definitions

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedSystem`: the system `(iₙ,* Fₙ)` in
  `D(𝒪_X)`, each term in degree `0`, and `…quasicoherentSystem`: the same system in
  `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.AffineCoheratorCase`: the affine case of the coherator, the input of
  the induction of `StacksFrontier/AlgebraicGeometry/Spaces/DerivedCoherator/`.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.isQuasiCompactSpace`,
  `…isAbsolutelySeparated`, `…isAbsolutelyQuasiSeparated`, `…isAffineHom_of_isAffineSpace`:
  the algebraic space of the situation is quasi-compact and separated, so every affine object
  étale over it maps to it by an affine morphism ([Stacks, Tag 08GB]).
* `…nonempty_iso_single_of_isDerivedLimit`: `R lim_{D(𝒪_X)} Fₙ` is concentrated in degree `0`,
  and `…exists_isKInjective_sectionsAmplitudeLE_zero`: it has affine amplitude `≤ 0`, both by
  [Stacks, Tag 0D3E], the transition maps being surjective.
* `AlgebraicGeometry.Space.isDerivedLimit_of_iso`, `…nonempty_iso_of_isDerivedLimit`: derived
  limits along isomorphic systems, and their uniqueness.
* `…derivedLimit_bounded_of_affineCase`: [Stacks, Tag 0CX5], from the affine case of the
  coherator.

## The proof

It is the source's, through Example [Stacks, Tag 0CST]: `DQ_X` is a right adjoint, so it carries
the derived limit `L = R lim_{D(𝒪_X)} Fₙ` to the derived limit in `D_QCoh(𝒪_X)`; `L` has affine
amplitude in `[0, 0]` (the source's `[0, 1]` is improved to `[0, 0]` by the surjectivity of the
transition maps, [Stacks, Tag 0D3E]); and the bounded cohomological dimension of `DQ_X`
([Stacks, Tag 0CSS], `AlgebraicGeometry.Space.exists_coheratorBound_of_affineCase`) bounds the
cohomology of `DQ_X(L)` from above, while its left t-exactness
(`AlgebraicGeometry.Space.coherator_vanishesBelow`) bounds it from below by `0`.

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] isGrothendieckAbelian_modules enoughInjectives_modules

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-! ### The geometry of the situation -/

/-- The inverse-limit base is affine. -/
theorem isAffine_limitBaseObject :
    IsAffine ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
      (limitBaseObject D.system D.B D.containsLimitBase)) :=
  inferInstanceAs (IsAffine (limitBase D.system))

/-- **`X` is quasi-compact**: it is of finite presentation, hence quasi-compact, over the affine
base `Spec A`. -/
theorem isQuasiCompactSpace : IsQuasiCompactSpace D.B D.S D.containsLimitBase D.X.left.1 :=
  isQuasiCompactSpace_source_of_isQuasiCompact D.B D.S D.containsLimitBase
    (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2
    (isQuasiCompactSpace_yoneda_of_isAffine D.B D.S D.containsLimitBase _
      D.isAffine_limitBaseObject) D.finitePresentation.2.1

/-- **`X` is a separated algebraic space**: it is separated over the affine base `Spec A`. -/
theorem isAbsolutelySeparated :
    IsAbsolutelySeparated D.B D.S D.containsLimitBase D.B.contains_terminal D.X.left.1 :=
  isAbsolutelySeparated_of_isSeparated_to_affine D.B D.S D.containsLimitBase D.B.contains_terminal
    _ D.isAffine_limitBaseObject D.X.hom.hom D.separated

/-- `X` is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated :
    IsAbsolutelyQuasiSeparated D.B D.S D.containsLimitBase D.B.contains_terminal D.X.left.1 :=
  isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated D.B D.S D.containsLimitBase
    D.B.contains_terminal _ D.isAbsolutelySeparated

/-- Every affine algebraic space étale over `X` maps to `X` by an affine morphism, `X` being
separated ([Stacks, Tag 08GB], part (4)). -/
theorem isAffineHom_of_isAffineSpace (V : SpacesEtale D.B D.S D.containsLimitBase D.X.left)
    (hV : IsAffineSpace D.B D.S D.containsLimitBase V.1.left.1) :
    IsAffineHom D.B D.S D.containsLimitBase V.1.hom.hom :=
  isAffineHom_of_isAffineSpace_source_of_isAbsolutelySeparated D.B D.S D.containsLimitBase
    D.B.contains_terminal _ hV D.isAbsolutelySeparated

/-! ### The system in the derived category -/

/-- **The system `(iₙ,* Fₙ)` read in `D(𝒪_X)`**, each term placed in degree `0`. Its derived limit
is `R lim_{D(𝒪_X)} Fₙ`. -/
abbrev derivedSystem : ℕᵒᵖ ⥤ spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left :=
  D.pushforwardSystem ⋙ spaceDerivedSingle D.B D.S D.containsLimitBase D.X.left 0

/-- The cohomology of `iₙ,* Fₙ`, placed in degree `0`, vanishes in every other degree. -/
private theorem isZero_homology_single_pushforwardModule (n : ℕ) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left q).obj
      ((spaceDerivedSingle D.B D.S D.containsLimitBase D.X.left 0).obj
        (D.pushforwardModule n))) := by
  let := spaceHasDerivedCategory D.B D.S D.containsLimitBase D.X.left
  rcases lt_or_gt_of_ne hq with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 q h
  · exact DerivedCategory.isZero_of_isLE _ 0 q h

/-- The terms of `derivedSystem` have quasi-coherent cohomology: the only nonzero one is
`iₙ,* Fₙ`, in degree `0`. -/
theorem spaceQuasicoherentProp_derivedSystem_obj (n : ℕ) :
    spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left (D.derivedSystem.obj (op n)) := by
  let := spaceHasDerivedCategory D.B D.S D.containsLimitBase D.X.left
  intro i
  by_cases hi : i = 0
  · subst hi
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
      (D.isQuasicoherentOnSite_pushforwardModule n)
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (D.isZero_homology_single_pushforwardModule n i hi)

/-- `D(𝒪_X)` has countable products, so the system has a derived limit. -/
instance hasProduct_derivedSystem :
    HasProduct fun n : ℕ => D.derivedSystem.obj ⟨n⟩ := by
  have := hasProductsOfShape_nat_derivedCategory_modules D.B D.S D.containsLimitBase
    D.X.left.1 D.X.left.2
  infer_instance

/-- The transition maps of the system are surjective on every cohomology sheaf. -/
theorem epi_homology_derivedSystem_map (n : ℕ) (q : ℤ) :
    Epi ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left q).map
      (D.derivedSystem.map (homOfLE (Nat.le_succ n)).op)) := by
  let := spaceHasDerivedCategory D.B D.S D.containsLimitBase D.X.left
  by_cases hq : q = 0
  · subst hq
    have hf : Epi (D.pushforwardSystem.map (homOfLE (Nat.le_succ n)).op) := by
      rw [pushforwardSystem_map_succ]
      exact D.epi_pushforwardTransition n
    let e := DerivedCategory.singleFunctorCompHomologyFunctorIso
      (Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2) 0
    have hnat := e.hom.naturality (D.pushforwardSystem.map (homOfLE (Nat.le_succ n)).op)
    rw [Functor.id_map] at hnat
    have h1 : Epi ((DerivedCategory.singleFunctor _ 0 ⋙ DerivedCategory.homologyFunctor _ 0).map
        (D.pushforwardSystem.map (homOfLE (Nat.le_succ n)).op) ≫ e.hom.app _) := by
      rw [hnat]
      exact epi_comp' (IsIso.epi_of_iso _) hf
    have h2 : Epi ((DerivedCategory.singleFunctor _ 0 ⋙ DerivedCategory.homologyFunctor _ 0).map
        (D.pushforwardSystem.map (homOfLE (Nat.le_succ n)).op)) := by
      simpa using epi_comp' h1 (IsIso.epi_of_iso (e.inv.app (D.pushforwardSystem.obj (op n))))
    exact h2
  · exact (D.isZero_homology_single_pushforwardModule n q hq).epi _

/-! ### The derived limit in `D(𝒪_X)` -/

/-- A limit cone over a diagram of zero objects has a zero cone point. -/
theorem isZero_pt_of_isLimit {J C : Type*} [Category J] [Category C] [HasZeroMorphisms C]
    {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) (hF : ∀ j, IsZero (F.obj j)) : IsZero c.pt :=
  (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun j => (hF j).eq_of_tgt _ _)

/-- Write `L = R lim_{D(𝒪_X)} Fₙ`. By [Stacks, Tag 0D3E], clause (1), `Hᵠ(L) = lim Hᵠ(iₙ,* Fₙ)`,
which vanishes for `q ≠ 0`. -/
theorem isZero_homology_of_isDerivedLimit
    (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (hL : IsDerivedLimit D.derivedSystem L) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left q).obj L) := by
  obtain ⟨_, -, _, -, ⟨hlim⟩⟩ := isLimit_cohomology_of_isDerivedLimit_of_epi D.B D.S
    D.containsLimitBase D.X.left.1 D.X.left.2 D.derivedSystem
    D.spaceQuasicoherentProp_derivedSystem_obj D.epi_homology_derivedSystem_map
    L hL q
  exact isZero_pt_of_isLimit hlim fun j => D.isZero_homology_single_pushforwardModule j.unop q hq

/-- `R lim_{D(𝒪_X)} Fₙ` is concentrated in degree `0`. -/
theorem nonempty_iso_single_of_isDerivedLimit
    (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (hL : IsDerivedLimit D.derivedSystem L) :
    Nonempty (L ≅ (spaceDerivedSingle D.B D.S D.containsLimitBase D.X.left 0).obj
      ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj L)) := by
  let := spaceHasDerivedCategory D.B D.S D.containsLimitBase D.X.left
  exact DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero L 0
    (D.isZero_homology_of_isDerivedLimit L hL)

/-- The higher cohomology over an affine étale chart of `H⁰(R lim Fₙ) = lim Fₙ` vanishes:
[Stacks, Tag 0D3E], clause (3). -/
theorem isZero_rightDerived_homology_of_isDerivedLimit
    (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (hL : IsDerivedLimit D.derivedSystem L) (V : SmallEtale D.B D.S D.containsLimitBase D.X.left.1)
    (hV : IsAffineChart D.B D.S D.containsLimitBase D.X.left.1 V) (p : ℕ) (hp : 0 < p) :
    IsZero (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2) V).rightDerived
        p).obj
        ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj L)) := by
  obtain ⟨_, -, _, -, ⟨hlim⟩⟩ := isLimit_cohomology_of_isDerivedLimit_of_epi D.B D.S
    D.containsLimitBase D.X.left.1 D.X.left.2 D.derivedSystem
    D.spaceQuasicoherentProp_derivedSystem_obj D.epi_homology_derivedSystem_map
    L hL 0
  have := hasProductsOfShape_nat_modules_ringUniverse D.B D.S D.containsLimitBase
    D.X.left.1 D.X.left.2
  exact (isZero_cohomology_limit_homology_of_isAffineChart_unconditional D.B D.S
    D.containsLimitBase D.X.left.1 D.X.left.2 D.derivedSystem
    D.spaceQuasicoherentProp_derivedSystem_obj D.epi_homology_derivedSystem_map
    0 V hV p hp).of_iso (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2) V).rightDerived
        p).mapIso
    (hlim.conePointUniqueUpToIso (limit.isLimit _)))

/-- **`R lim_{D(𝒪_X)} Fₙ` has affine amplitude `≤ 0`**: it is represented by a K-injective
complex, the extended injective resolution of `H⁰(R lim Fₙ) = lim Fₙ`, whose complexes of
sections over the affine étale charts have no cohomology in positive degrees, by
[Stacks, Tag 0D3E], clause (3). -/
theorem exists_isKInjective_sectionsAmplitudeLE_zero
    (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (hL : IsDerivedLimit D.derivedSystem L) :
    ∃ (I : CochainComplex (Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2) ℤ)
      (_ : I.IsKInjective),
        Nonempty ((spaceDerivedQ D.B D.S D.containsLimitBase D.X.left).obj I ≅ L) ∧
        SectionsAmplitudeLE D.B D.S D.containsLimitBase D.X.left 0 I := by
  let := spaceHasDerivedCategory D.B D.S D.containsLimitBase D.X.left
  let M0 := (spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj L
  let I := (injectiveResolution M0).cochainComplex
  obtain ⟨e⟩ := D.nonempty_iso_single_of_isDerivedLimit L hL
  refine ⟨I, CochainComplex.isKInjective_of_injective _ 0,
    ⟨((DerivedCategory.quotientCompQhIso _).app I).symm ≪≫
      ((Stacks.DerivedFunctor.singleIsoResCompQh).app M0).symm ≪≫ e.symm⟩, ?_⟩
  intro V hV i hi
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = i := ⟨i.toNat, by omega⟩
  exact (D.isZero_rightDerived_homology_of_isDerivedLimit L hL V hV p (by omega)).of_iso
    (((Stacks.DerivedIndexing.rightDerivedIsoRes
      (Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
        (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2) V) p).app M0) ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ (p : ℤ)).app _).symm

end FlatSheafExistenceSituation

/-! ### Derived limits along isomorphic systems -/

section Transport

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A derived limit of a system is a derived limit of every isomorphic system. -/
theorem isDerivedLimit_of_iso {F F' : ℕᵒᵖ ⥤ C} (e : F ≅ F')
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] [HasProduct fun n : ℕ => F'.obj ⟨n⟩] {K : C}
    (hK : IsDerivedLimit F K) : IsDerivedLimit F' K := by
  obtain ⟨p, δ, hT⟩ := hK
  let eP : (∏ᶜ fun n : ℕ => F.obj ⟨n⟩) ≅ ∏ᶜ fun n : ℕ => F'.obj ⟨n⟩ :=
    { hom := Limits.Pi.map fun n => (e.app ⟨n⟩).hom
      inv := Limits.Pi.map fun n => (e.app ⟨n⟩).inv
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp }
  refine ⟨p ≫ eP.hom, eP.inv ≫ δ, isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) eP.symm eP.symm (by simp) ?_ (by simp)
  dsimp only [Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₂, Iso.symm_hom]
  refine Limits.Pi.hom_ext _ _ fun n => ?_
  simp only [eP, Category.assoc, Pi.lift_π, Limits.Pi.map_π, Preadditive.comp_sub,
    Preadditive.sub_comp, Pi.lift_π_assoc, Limits.Pi.map_π_assoc]
  congr 1
  have h := e.inv.naturality (homOfLE (Nat.le_succ n)).op
  simp only [Iso.app_inv] at h ⊢
  rw [h]

/-- Derived limits are unique up to isomorphism: both are the fibre of the same difference map
of products. -/
theorem nonempty_iso_of_isDerivedLimit {F : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    {K K' : C} (hK : IsDerivedLimit F K) (hK' : IsDerivedLimit F K') : Nonempty (K ≅ K') := by
  obtain ⟨p, δ, hT⟩ := hK
  obtain ⟨p', δ', hT'⟩ := hK'
  obtain ⟨e, -, -⟩ := exists_iso_of_arrow_iso _ _ (rot_of_distTriang _ hT)
    (rot_of_distTriang _ hT') (Iso.refl _)
  exact ⟨(shiftFunctor C (1 : ℤ)).preimageIso (Triangle.π₃.mapIso e)⟩

end Transport

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- The system `(iₙ,* Fₙ)` read in `D_QCoh(𝒪_X)`. -/
abbrev quasicoherentSystem :
    ℕᵒᵖ ⥤ (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory :=
  (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).lift D.derivedSystem
    fun n => D.spaceQuasicoherentProp_derivedSystem_obj n.unop

/-- **The affine case of the coherator**, the input the induction of
`StacksFrontier/AlgebraicGeometry/Spaces/DerivedCoherator/` runs on: on an affine algebraic space
every object of `D(𝒪_Y)` is coreflective, every object of `D_QCoh(𝒪_Y)` is represented by a
complex of quasi-coherent modules, and the coreflection of a K-injective complex of affine
amplitude at most `b` lies in degrees `≤ b`. -/
def AffineCoheratorCase (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ Y : AlgebraicSpaces B S hS, IsAffineSpace B S hS Y.1 →
    (∀ K, spaceCoreflective B S hS Y K) ∧
    (∀ E, spaceQuasicoherentProp B S hS Y E →
      ∃ (C : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
        (_ : ∀ n, (C.X n).IsQuasicoherentOnSite), Nonempty ((spaceDerivedQ B S hS Y).obj C ≅ E)) ∧
    ∀ (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ), I.IsKInjective →
      SectionsAmplitudeLE B S hS Y b I →
        ∃ (E Q' : spaceDerivedCategory B S hS Y) (a : E ⟶ (spaceDerivedQ B S hS Y).obj I)
          (b' : (spaceDerivedQ B S hS Y).obj I ⟶ Q') (c : Q' ⟶ E⟦(1 : ℤ)⟧),
          Triangle.mk a b' c ∈ distTriang _ ∧ spaceQuasicoherentProp B S hS Y E ∧
            (spaceQuasicoherentProp B S hS Y).rightOrthogonal Q' ∧
            SpaceCohomologyVanishesAbove B S hS Y b E

/-- **[Stacks, Tag 0CX5], granted the affine case of the coherator.** In Situation 0CX4 the
inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint `DQ_X`, the system `(Fₙ)` has a derived limit
`L = R lim_{D(𝒪_X)} Fₙ`, and for every such `L` and every coherator `DQ_X`, `K = DQ_X(L)` is a
derived limit of `(Fₙ)` in `D_QCoh(𝒪_X)` with cohomology sheaves vanishing in negative degrees and
above some degree. -/
theorem derivedLimit_bounded_of_affineCase
    (haffine : AffineCoheratorCase D.B D.S D.containsLimitBase) :
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.IsLeftAdjoint ∧
    (∃ L, IsDerivedLimit D.derivedSystem L) ∧
    (∀ (DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
        (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory)
      (_ : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
      (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left),
      IsDerivedLimit D.derivedSystem L →
        (∃ _ : HasProduct fun n : ℕ => D.quasicoherentSystem.obj ⟨n⟩,
          IsDerivedLimit D.quasicoherentSystem (DQ.obj L)) ∧
        SpaceCohomologyVanishesBelow D.X.left 0
          ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L)) ∧
        ∃ c : ℤ, SpaceCohomologyVanishesAbove D.B D.S D.containsLimitBase D.X.left c
          ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L))) ∧
    ∀ (_ : HasProduct fun n : ℕ => D.quasicoherentSystem.obj ⟨n⟩)
      (K : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory),
      IsDerivedLimit D.quasicoherentSystem K →
        SpaceCohomologyVanishesBelow D.X.left 0
          ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj K) ∧
        ∃ c : ℤ, SpaceCohomologyVanishesAbove D.B D.S D.containsLimitBase D.X.left c
          ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj K) := by
  have hcor := spaceCoreflective_of_affineCase D.B.contains_terminal D.X.left D.isQuasiCompactSpace
    D.isAbsolutelyQuasiSeparated D.isAffineHom_of_isAffineSpace
    (fun Y hY => ⟨(haffine Y hY).1, (haffine Y hY).2.1⟩)
  have hadj := isLeftAdjoint_spaceQuasicoherentι_of_forall hcor
  have hL := exists_isDerivedLimit D.derivedSystem
  let P := spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left
  have hmain : ∀ (DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
        P.FullSubcategory) (_ : P.ι ⊣ DQ)
      (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left),
      IsDerivedLimit D.derivedSystem L →
        (∃ _ : HasProduct fun n : ℕ => D.quasicoherentSystem.obj ⟨n⟩,
          IsDerivedLimit D.quasicoherentSystem (DQ.obj L)) ∧
        SpaceCohomologyVanishesBelow D.X.left 0 (P.ι.obj (DQ.obj L)) ∧
        ∃ c : ℤ, SpaceCohomologyVanishesAbove D.B D.S D.containsLimitBase D.X.left c
          (P.ι.obj (DQ.obj L)) := by
    intro DQ adj L hL
    let : DQ.CommShift ℤ := adj.rightAdjointCommShift ℤ
    let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
    have : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
    have : DQ.IsRightAdjoint := adj.isRightAdjoint
    have : DQ.IsTriangulated := adj.isTriangulated_rightAdjoint
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨h, hDL⟩ := Stacks.Injectives.isDerivedLimit_map_rightAdjoint DQ D.derivedSystem L hL
      let e : D.derivedSystem ⋙ DQ ≅ D.quasicoherentSystem :=
        Functor.isoWhiskerRight (P.liftCompιIso D.derivedSystem _).symm DQ ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (asIso adj.unit).symm ≪≫
          Functor.rightUnitor _
      have : HasProduct fun n : ℕ => (D.derivedSystem ⋙ DQ).obj ⟨n⟩ := h
      have : HasProduct fun n : ℕ => D.quasicoherentSystem.obj ⟨n⟩ :=
        hasLimit_of_iso (F := Discrete.functor fun n : ℕ => (D.derivedSystem ⋙ DQ).obj ⟨n⟩)
          (Discrete.natIso fun n => e.app ⟨n.as⟩)
      exact ⟨inferInstance, isDerivedLimit_of_iso e hDL⟩
    · refine coherator_vanishesBelow adj 0 L fun i hi => ?_
      exact D.isZero_homology_of_isDerivedLimit L hL i (by omega)
    · obtain ⟨N, hN⟩ := exists_coheratorBound_of_affineCase adj D.B.contains_terminal
        D.isQuasiCompactSpace D.isAbsolutelyQuasiSeparated D.isAffineHom_of_isAffineSpace
        (fun Y hY => ⟨(haffine Y hY).2.1, (haffine Y hY).2.2⟩)
      obtain ⟨I, hI, ⟨eI⟩, hamp⟩ := D.exists_isKInjective_sectionsAmplitudeLE_zero L hL
      exact ⟨0 + N, (hN 0 I hI hamp).of_iso ((DQ ⋙ P.ι).mapIso eI)⟩
  refine ⟨hadj, hL, hmain, fun hprod K hK => ?_⟩
  obtain ⟨L, hL'⟩ := hL
  obtain ⟨⟨h', hDL⟩, hge, c, hle⟩ := hmain _ (Adjunction.ofIsLeftAdjoint P.ι) L hL'
  obtain ⟨e⟩ := nonempty_iso_of_isDerivedLimit hDL hK
  have hiso := fun i => ((spaceDerivedHomology D.B D.S D.containsLimitBase
    D.X.left i).mapIso (P.ι.mapIso e)).symm
  exact ⟨fun i hi => (hge i hi).of_iso (hiso i), c, fun i hi => (hle i hi).of_iso (hiso i)⟩

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
