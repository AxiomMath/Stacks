module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower.LimitCohomology
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower.LimitCohomology

/-!
# Finiteness of the limit cohomology of a perfect tower

The tower restricted to `ℤ_[ℓ]`, its perfect derived limit, the comparison of the cohomology of
the derived limit with `Hⁱ_∞`, and the finiteness of each `Hⁱ_∞` as a `ℤ_[ℓ]`-module
(Stacks 03V4, part (2)).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Trace
open scoped BigOperators TensorProduct

universe u w v

namespace Stacks.InverseSystem

open CategoryTheory.FilteredDerived (finite_nonzero_degrees)

attribute [local instance] HasDerivedCategory.standard

/-! ### The ℓ-adic limit of the tower -/

private def coefficientDiagram (ℓ : ℕ) : ℕᵒᵖ ⥤ CommRingCat where
  obj n := CommRingCat.of (ZMod (ℓ ^ (n.unop + 1)))
  map f := CommRingCat.ofHom (ZMod.castHom
    (pow_dvd_pow ℓ (Nat.add_le_add_right (leOfHom f.unop) 1)) _)
  map_id _ := by apply CommRingCat.hom_ext; exact Subsingleton.elim _ _
  map_comp _ _ := by apply CommRingCat.hom_ext; exact Subsingleton.elim _ _
private def coefficientCone (ℓ : ℕ) [Fact ℓ.Prime] : Cone (coefficientDiagram ℓ) where
  pt := CommRingCat.of ℤ_[ℓ]
  π :=
    { app := fun n => CommRingCat.ofHom (PadicInt.toZModPow (n.unop + 1))
      naturality := by
        intro n m f
        ext x
        exact (PadicInt.cast_toZModPow (m.unop + 1) (n.unop + 1)
          (Nat.add_le_add_right (leOfHom f.unop) 1) x).symm }
private def coefficientConeIsLimit (ℓ : ℕ) [Fact ℓ.Prime] :
    IsLimit (coefficientCone ℓ) := by
  letI : Subsingleton (ZMod (ℓ ^ 0)) := by
    simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
  let fs (s : Cone (coefficientDiagram ℓ)) : (n : ℕ) → s.pt →+* ZMod (ℓ ^ n)
    | 0 => (ZMod.castHom (pow_dvd_pow ℓ (Nat.zero_le 1)) _).comp (s.π.app (Opposite.op 0)).hom
    | n + 1 => (s.π.app (Opposite.op n)).hom
  have hf (s : Cone (coefficientDiagram ℓ)) (m n : ℕ) (h : m ≤ n) :
      (ZMod.castHom (pow_dvd_pow ℓ h) _).comp (fs s n) = fs s m := by
    cases m with
    | zero => ext; exact Subsingleton.elim _ _
    | succ m =>
      cases n with
      | zero => omega
      | succ n =>
        exact congrArg CommRingCat.Hom.hom
          (s.w (homOfLE (by omega : m ≤ n)).op)
  refine
    { lift := fun s => CommRingCat.ofHom (PadicInt.lift (hf s))
      fac := ?_
      uniq := ?_ }
  · intro s n
    exact congrArg CommRingCat.ofHom (PadicInt.lift_spec (hf s) (n.unop + 1))
  · intro s m hm
    apply CommRingCat.hom_ext
    symm
    apply PadicInt.lift_unique (hf s)
    intro n
    cases n with
    | zero => ext; exact Subsingleton.elim _ _
    | succ n => exact congrArg CommRingCat.Hom.hom (hm (Opposite.op n))
private abbrev padicRestriction {ℓ : ℕ} [Fact ℓ.Prime] (n : ℕ) :=
  (ModuleCat.restrictScalars.{v} (PadicInt.toZModPow (p := ℓ) (n + 1))).mapDerivedCategory
private abbrev restrictedTowerObj {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (n : ℕ) :=
  (padicRestriction.{v} (ℓ := ℓ) n).obj (T.obj n)
private def restrictedTowerTransition {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (n : ℕ) :
    restrictedTowerObj T (n + 1) ⟶ restrictedTowerObj T n :=
  (padicRestriction.{v} (ℓ := ℓ) (n + 1)).map (T.transition n) ≫
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp
      (PadicInt.toZModPow (n + 1 + 1)) (levelCast ℓ n) (PadicInt.toZModPow (n + 1))
      (by
        ext x
        exact (PadicInt.cast_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _) x).symm)).hom.app
      (T.obj n)
private abbrev restrictedTower {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) :=
  Functor.ofOpSequence (restrictedTowerTransition T)
-- `restrictHomologyIsoOfHom` at `Kₙ`, stated at the spelling its consumers use:
-- `restrictedTowerObj` on the source and `ModuleCat.of ℤ_[ℓ] (levelCohomology _ _ _)` on the
-- target.  Taking the `app` directly leaves both ends spelled through `⋙`, which is the same
-- object only up to unfolding `Functor.comp` and `ModuleCat.restrictScalars`.
private def restrictedHomologyIso {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ)
    (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).obj (restrictedTowerObj T n) ≅
      ModuleCat.of ℤ_[ℓ] (levelCohomology T i n) :=
  (restrictHomologyIsoOfHom.{v} (PadicInt.toZModPow (n + 1)) i).app (T.obj n)
-- Stacks 0CQG applied to the coefficient tower `ℤ/ℓⁿ⁺¹ℤ` with limit `ℤ_[ℓ]`, restated in terms
-- of `restrictedTowerObj` and `restrictedTowerTransition`.  Both consumers go through this one
-- specialisation: matching the general statement's product diagram against this file's is a
-- large defeq problem, and it is paid here once.
--
-- `ZMod` is opaque for it.  `ZMod` is defined by cases on its modulus, so each
-- `ZMod (ℓ ^ a) =?= ZMod (ℓ ^ b)` the match throws up that is not already syntactic sends the
-- elaborator off to evaluate `ℓ ^ a`, i.e. to unfold `Nat.pow` and `Nat.rec` at a variable
-- exponent, where no progress is possible.  Over this one declaration there are 27,975 such
-- comparisons, 200,770 `Nat.pow` and 602,056 `Nat.rec` unfoldings.  With `ZMod` irreducible
-- the modulus is compared as the natural number it is, and nothing needs the rest.
section
attribute [local irreducible] ZMod

private lemma isPerfect_and_baseChange_isIso {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ)
    [HasProduct (restrictedTowerObj T)] (K : DerivedCategory (ModuleCat.{v} ℤ_[ℓ]))
    (p : K ⟶ ∏ᶜ (restrictedTowerObj T)) (δ : ∏ᶜ (restrictedTowerObj T) ⟶ K⟦(1 : ℤ)⟧)
    (h : Pretriangulated.Triangle.mk p (Pi.lift (fun n => Pi.π (restrictedTowerObj T) n -
      Pi.π (restrictedTowerObj T) (n + 1) ≫ restrictedTowerTransition T n)) δ ∈ distTriang _) :
    StacksDraft.Perfect.IsPerfect K ∧
      ∀ n, IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison
        (PadicInt.toZModPow (n + 1)) (p ≫ Pi.π (restrictedTowerObj T) n)) :=
  StacksDraft.DerivedInverseLimit.derivedLimit_isPerfect_and_baseChange_iso
    (coefficientDiagram ℓ) (coefficientCone ℓ) (coefficientConeIsLimit ℓ)
    T.obj T.transition
    (fun n => ZMod.castHom_surjective (pow_dvd_pow ℓ (Nat.le_succ (n + 1))))
    (fun n => StacksDraft.DerivedInverseLimit.isLocallyNilpotent_of_isNilpotent _
      (isNilpotent_ker_levelCast n))
    (Or.inl T.isPerfect) T.comparison_isIso K p δ h

end

private lemma exists_perfect_derivedLimit {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) :
    ∃ K : DerivedCategory (ModuleCat.{v} ℤ_[ℓ]),
      StacksDraft.Perfect.IsPerfect K ∧
        Pretriangulated.IsDerivedLimit (restrictedTower T) K := by
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} ℤ_[ℓ]) :=
    moduleCat_hasExactLimitsOfShape_discrete ℤ_[ℓ] ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} ℤ_[ℓ])) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨K, p, δ, hK⟩ := Pretriangulated.exists_isDerivedLimit (restrictedTower T)
  refine ⟨K, ?_, p, δ, hK⟩
  apply (isPerfect_and_baseChange_isIso T K p δ ?_).1
  simp only [restrictedTower, Functor.ofOpSequence_map_homOfLE_succ] at hK
  exact hK

private lemma finite_homology_of_perfect {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{v} R)) (hK : StacksDraft.Perfect.IsPerfect K) (i : ℤ) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨e⟩⟩ := hK
  have : Module.Finite R (P.X i) := hf i
  have : Module.Finite R (P.cycles i) :=
    Module.Finite.of_injective (P.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have : Module.Finite R (P.homology i) :=
    Module.Finite.of_surjective (P.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have : Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.up ℤ) i).obj P) := by
    show Module.Finite R (P.homology i)
    infer_instance
  exact Module.Finite.equiv
    (((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e) ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P).symm.toLinearEquiv
private lemma finite_limit_homology_of_perfect_derivedLimit
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} R))
    (K : DerivedCategory (ModuleCat.{v} R))
    (hperf : StacksDraft.Perfect.IsPerfect K) (hK : Pretriangulated.IsDerivedLimit F K)
    (i : ℤ) :
    Module.Finite R (↑(limit (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} R) i) :
      ModuleCat.{v} R)) := by
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} R) :=
    moduleCat_hasExactLimitsOfShape_discrete R ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨a, b, htri, h⟩ := DerivedCategory.isDerivedLimit_homology_shortExact F K hK
  obtain ⟨e, j, q, w, he, hj, hq, hs⟩ := h i
  have : Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) :=
    finite_homology_of_perfect K hperf i
  exact Module.Finite.of_surjective q.hom ((ModuleCat.epi_iff_surjective q).mp hs.epi_g)


-- The four data fields of `ShortComplex.LeftHomologyData.map`.  Mathlib derives `map_f'` but
-- leaves these implicit in the definition, so `((h.map F).map G).K` is `G.obj (F.obj h.K)` only
-- after `map` is unfolded -- and that is what makes a left homology map data between
-- `(h.map F).map G` and `h.map (F ⋙ G)` unreadable below.
section LeftHomologyDataMap

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  {S : ShortComplex C} (h : S.LeftHomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
  [h.IsPreservedBy F]

private lemma leftHomologyData_map_K : (h.map F).K = F.obj h.K := rfl

private lemma leftHomologyData_map_H : (h.map F).H = F.obj h.H := rfl

private lemma leftHomologyData_map_i : (h.map F).i = F.map h.i := rfl

private lemma leftHomologyData_map_π : (h.map F).π = F.map h.π := rfl

end LeftHomologyDataMap

private lemma mapHomologyIso_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
      (S.mapHomologyIso (F ⋙ G)).hom := by
  let h₁ := (S.homologyData.left.map F).map G
  let h₂ := S.homologyData.left.map (F ⋙ G)
  let d : ShortComplex.LeftHomologyMapData (𝟙 (S.map (F ⋙ G))) h₁ h₂ :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by
        simp [h₁, h₂, leftHomologyData_map_K]
      commf' := by
        simp [h₁, h₂, leftHomologyData_map_K, ShortComplex.LeftHomologyData.map_f']
      commπ := by
        simp [h₁, h₂, leftHomologyData_map_K, leftHomologyData_map_H] }
  have hm : (S.mapHomologyIso (F ⋙ G)).hom = h₁.homologyIso.hom := by
    have h := d.homologyMap_comm
    simp only [ShortComplex.homologyMap_id, Category.id_comp] at h
    exact h.trans (Category.comp_id _)
  -- Pure iso algebra, proved where the two spellings of `h₁.H` cannot be seen: the `Iso.trans`
  -- that `mapHomologyIso_eq` produces has its middle object spelled `((h.map F).map G).H` while
  -- everything composed with it says `G.obj (F.obj S.homology)`.
  have iso_cancel {X Y Z : E} (α : X ≅ Y) (γ : Z ≅ Y) :
      (α ≪≫ γ.symm).hom ≫ γ.hom = α.hom := by simp
  rw [S.homologyData.left.map F |>.mapHomologyIso_eq G, hm]
  exact iso_cancel h₁.homologyIso (G.mapIso (S.mapHomologyIso F))

-- `(DerivedCategory.homologyFunctorFactors C i).symm.app P`, with its source spelled
-- `HomologicalComplex.homology` and its target `homologyFunctor.obj (Q.obj _)` -- the two
-- shapes the goals below present.  Taking the `symm.app` directly leaves every isomorphism
-- assembled from it ill-typed at `implicit` transparency, so no rewrite can pass through one.
-- `homologyMap_comp_homologyFactors` is the `inv` counterpart of Mathlib's
-- `DerivedCategory.homologyFunctorFactors_hom_naturality`.
private def homologyFactors {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (P : CochainComplex C ℤ) (i : ℤ) :
    P.homology i ≅ (DerivedCategory.homologyFunctor C i).obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.homologyFunctorFactors C i).symm.app P

private lemma homologyMap_comp_homologyFactors {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {P P' : CochainComplex C ℤ} (f : P ⟶ P') (i : ℤ) :
    HomologicalComplex.homologyMap f i ≫ (homologyFactors P' i).hom =
      (homologyFactors P i).hom ≫
        (DerivedCategory.homologyFunctor C i).map (DerivedCategory.Q.map f) :=
  (DerivedCategory.homologyFunctorFactors C i).inv.naturality f

-- `ShortComplex.mapHomologyIso` for the degree-`i` short complex of a cochain complex, with
-- both ends spelled `HomologicalComplex.homology`, for the same reason.
private def mapHomologyFactors {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (P : CochainComplex C ℤ) (i : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology i ≅ F.obj (P.homology i) :=
  (P.sc i).mapHomologyIso F

-- `Functor.mapDerivedCategoryFactors` at one object, written applied on both ends, for the
-- same reason: its `.app` can only be spelled through the `⋙` of the two functors.
private def restrictDerivedFactors {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (P : CochainComplex (ModuleCat.{v} S) ℤ) :
    (ModuleCat.restrictScalars.{v} f).mapDerivedCategory.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{v} f).mapHomologicalComplex (.up ℤ)).obj P) :=
  (ModuleCat.restrictScalars.{v} f).mapDerivedCategoryFactors.app P

-- `ModuleCat.restrictScalarsComp'` at one object, written applied on both ends.
private def restrictScalarsCompApp {R S A : Type} [CommRing R] [CommRing S] [CommRing A]
    (f : R →+* S) (g : S →+* A) (M : ModuleCat.{v} A) :
    (ModuleCat.restrictScalars.{v} f).obj ((ModuleCat.restrictScalars.{v} g).obj M) ⟶
      (ModuleCat.restrictScalars.{v} (g.comp f)).obj M :=
  (ModuleCat.restrictScalarsComp'.{v} f g (g.comp f) rfl).inv.app M

-- `restrictHomologyIsoOfHom` at one object, with both ends written applied.  Its `.app` can
-- only ever be spelled through the `⋙` of the two functors it is a natural transformation of,
-- while everything composed with it says `homologyFunctor.obj (mapDerivedCategory.obj _)` and
-- `restrictScalars.obj (homologyFunctor.obj _)`; no `rw` can bridge the two.
private def restrictHomologyApp {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{v} S)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
        ((ModuleCat.restrictScalars.{v} f).mapDerivedCategory.obj K) ⟶
      (ModuleCat.restrictScalars.{v} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} S) i).obj K) :=
  (restrictHomologyIsoOfHom.{v} f i).hom.app K

private lemma restrictHomologyIsoOfHom_hom_app_Q {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (i : ℤ) (P : CochainComplex (ModuleCat.{v} S) ℤ) :
    restrictHomologyApp.{v} f i (DerivedCategory.Q.obj P) =
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        (restrictDerivedFactors.{v} f P).hom ≫
      (homologyFactors
        (((ModuleCat.restrictScalars.{v} f).mapHomologicalComplex (.up ℤ)).obj P) i).inv ≫
      (mapHomologyFactors (ModuleCat.restrictScalars.{v} f) P i).hom ≫
      (ModuleCat.restrictScalars.{v} f).map (homologyFactors P i).hom := by
  dsimp only [restrictHomologyApp, restrictDerivedFactors, homologyFactors, mapHomologyFactors,
    HomologicalComplex.homologyFunctor, HomologicalComplex.shortComplexFunctor,
    ShortComplex.homologyFunctor]
  simp [restrictHomologyIsoOfHom, Localization.liftNatIso, Localization.Lifting.iso,
    Category.assoc, ShortComplex.homologyFunctorIso, Functor.isoWhiskerLeft,
    Functor.isoWhiskerRight, Iso.trans, Iso.symm, Functor.associator,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  all_goals dsimp only [HomologicalComplex.homologyFunctor,
    HomologicalComplex.shortComplexFunctor, ShortComplex.homologyFunctor]
  all_goals simp
  all_goals rfl


private lemma restrictHomologyIsoOfHom_comp_Q
    {R S A : Type} [CommRing R] [CommRing S] [CommRing A]
    (f : R →+* S) (g : S →+* A) (i : ℤ)
    (P : CochainComplex (ModuleCat.{v} A) ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        ((StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, v}
          f g (g.comp f) rfl).hom.app (DerivedCategory.Q.obj P)) ≫
      restrictHomologyApp.{v} (g.comp f) i (DerivedCategory.Q.obj P) =
    restrictHomologyApp.{v} f i
        ((ModuleCat.restrictScalars.{v} g).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
      (ModuleCat.restrictScalars.{v} f).map
        (restrictHomologyApp.{v} g i (DerivedCategory.Q.obj P)) ≫
      restrictScalarsCompApp.{v} f g
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
          (DerivedCategory.Q.obj P)) := by
  let e := Functor.mapHomologicalComplexCompIso
    (ModuleCat.restrictScalarsComp'.{v} f g (g.comp f) rfl).symm (.up ℤ)
  -- Nothing below is abbreviated by a `let`: the goal spells `ModuleCat.restrictScalars f` and
  -- `DerivedCategory.homologyFunctor _ i` out, and a local definition standing for one of them
  -- is a different term to every `rw` that follows.
  have he : (restrictDerivedFactors.{v} f
        (((ModuleCat.restrictScalars.{v} g).mapHomologicalComplex (.up ℤ)).obj P)).inv ≫
      (ModuleCat.restrictScalars.{v} f).mapDerivedCategory.map
          (restrictDerivedFactors.{v} g P).inv ≫
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, v}
          f g (g.comp f) rfl).hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map (e.hom.app P) ≫
        (restrictDerivedFactors.{v} (g.comp f) P).inv := by
    simp [StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp, e,
      restrictDerivedFactors, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  -- `refine`, not `rw [← cancel_epi _]`: the two sides of the statement spell their common
  -- source `Hⁱ((F.mapDerivedCategory ⋙ G.mapDerivedCategory).obj (Q.obj P))` and
  -- `Hⁱ(G.mapDerivedCategory.obj (F.mapDerivedCategory.obj (Q.obj P)))`, so the equation
  -- `cancel_epi` has to match is not type-correct at `implicit` transparency.
  refine (cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
    ((restrictDerivedFactors.{v} f
        (((ModuleCat.restrictScalars.{v} g).mapHomologicalComplex (.up ℤ)).obj P)).inv ≫
      (ModuleCat.restrictScalars.{v} f).mapDerivedCategory.map
        (restrictDerivedFactors.{v} g P).inv))).mp ?_
  dsimp only [Functor.comp_obj]
  rw [← Functor.map_comp_assoc, Category.assoc, he]
  rw [Functor.map_comp, Category.assoc]
  rw [restrictHomologyIsoOfHom_hom_app_Q]
  simp only [Functor.map_comp, Category.assoc, Functor.comp_obj]
  rw [Iso.map_inv_hom_id_assoc]
  -- Naturality, restated at the applied spelling: a `have` is checked at `default`
  -- transparency, so it is the one place the two spellings may meet.
  have hn : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        ((ModuleCat.restrictScalars.{v} f).mapDerivedCategory.map
          (restrictDerivedFactors.{v} g P).inv) ≫
      restrictHomologyApp.{v} f i
        ((ModuleCat.restrictScalars.{v} g).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) =
      restrictHomologyApp.{v} f i (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars.{v} g).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (ModuleCat.restrictScalars.{v} f).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} S) i).map
            (restrictDerivedFactors.{v} g P).inv) :=
    (restrictHomologyIsoOfHom.{v} f i).hom.naturality
      ((ModuleCat.restrictScalars.{v} g).mapDerivedCategoryFactors.inv.app P)
  rw [reassoc_of% hn]
  rw [restrictHomologyIsoOfHom_hom_app_Q, restrictHomologyIsoOfHom_hom_app_Q]
  simp only [Functor.map_comp, Category.assoc]
  rw [Iso.map_inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc _
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} S) i).map
      (restrictDerivedFactors.{v} g P).inv)
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} S) i).map
      (restrictDerivedFactors.{v} g P).hom),
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.map_hom_inv_id_assoc]
  have heid : e.hom.app P = 𝟙 _ := by ext j x; rfl
  -- `heid` identifies two spellings of a single object, so the morphism it replaces by an
  -- identity has its two ends spelled differently.  Cancelling it is therefore stated once as
  -- a composite, whose `exact` runs at `default` transparency.
  have hid {Z : ModuleCat.{v} R}
      (w : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{v} (g.comp f)).mapHomologicalComplex
          (.up ℤ)).obj P)) ⟶ Z) :
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        (DerivedCategory.Q.map (e.hom.app P)) ≫ w = w := by
    rw [show (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        (DerivedCategory.Q.map (e.hom.app P)) = 𝟙 _ from
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).congr_map
          ((DerivedCategory.Q.congr_map heid).trans (DerivedCategory.Q.map_id _))).trans
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map_id _)]
    exact Category.id_comp w
  rw [hid]
  show (homologyFactors (((ModuleCat.restrictScalars.{v} (g.comp f)).mapHomologicalComplex
        (.up ℤ)).obj P) i).inv ≫
      ((P.sc i).mapHomologyIso
          (ModuleCat.restrictScalars.{v} g ⋙ ModuleCat.restrictScalars.{v} f)).hom ≫
        (ModuleCat.restrictScalars.{v} f).map ((ModuleCat.restrictScalars.{v} g).map
          (homologyFactors P i).hom) = _
  -- No `Category.assoc` here: it would have to see `P.homology i` and `(P.sc i).homology` as
  -- one object.  In `ModuleCat` associativity of composition is definitional, so the `rfl`
  -- that closes the goal reassociates on its own -- and absorbs the comparison
  -- `restrictScalarsCompApp`, which is the identity.
  rw [← mapHomologyIso_comp (P.sc i) (ModuleCat.restrictScalars.{v} g)
    (ModuleCat.restrictScalars.{v} f)]
  rfl

lemma restrictHomologyIsoOfHom_comp
    {R S A : Type} [CommRing R] [CommRing S] [CommRing A]
    (f : R →+* S) (g : S →+* A) (h : R →+* A) (w : h = g.comp f) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{v} A)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        ((StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, v}
          f g h w).hom.app K) ≫ (restrictHomologyIsoOfHom.{v} h i).hom.app K =
    (restrictHomologyIsoOfHom.{v} f i).hom.app
        ((ModuleCat.restrictScalars.{v} g).mapDerivedCategory.obj K) ≫
      (ModuleCat.restrictScalars.{v} f).map ((restrictHomologyIsoOfHom.{v} g i).hom.app K) ≫
      (ModuleCat.restrictScalarsComp'.{v} f g h w).inv.app
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K) := by
  subst h
  let F := ModuleCat.restrictScalars.{v} g
  let G := ModuleCat.restrictScalars.{v} f
  let H := ModuleCat.restrictScalars.{v} (g.comp f)
  let HR := DerivedCategory.homologyFunctor (ModuleCat.{v} R) i
  let HS := DerivedCategory.homologyFunctor (ModuleCat.{v} S) i
  let HA := DerivedCategory.homologyFunctor (ModuleCat.{v} A) i
  let α : (F.mapDerivedCategory ⋙ G.mapDerivedCategory) ⋙ HR ⟶ HA ⋙ H :=
    Functor.whiskerRight (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, v}
      f g (g.comp f) rfl).hom HR ≫ (restrictHomologyIsoOfHom (g.comp f) i).hom
  let β : (F.mapDerivedCategory ⋙ G.mapDerivedCategory) ⋙ HR ⟶ HA ⋙ H :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft F.mapDerivedCategory (restrictHomologyIsoOfHom f i).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (restrictHomologyIsoOfHom g i).hom G ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft HA (ModuleCat.restrictScalarsComp'.{v} f g (g.comp f) rfl).inv
  have hQ (P : CochainComplex (ModuleCat.{v} A) ℤ) :
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P) := by
    show HR.map ((StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, v}
      f g (g.comp f) rfl).hom.app (DerivedCategory.Q.obj P)) ≫
      (restrictHomologyIsoOfHom (g.comp f) i).hom.app (DerivedCategory.Q.obj P) = _
    dsimp only [β, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj]
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
    exact restrictHomologyIsoOfHom_comp_Q f g i P
  have hab : α = β := by
    apply NatTrans.ext
    funext X
    let P := DerivedCategory.Q.objPreimage X
    let e := DerivedCategory.Q.objObjPreimageIso X
    apply (cancel_epi (((F.mapDerivedCategory ⋙ G.mapDerivedCategory) ⋙ HR).map e.hom)).mp
    rw [α.naturality, β.naturality, hQ P]
  simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp] using congrArg (fun η => η.app K) hab

private abbrev cohomologyDiagram {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ) :
    ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ] :=
  Functor.ofOpSequence (X := fun n => ModuleCat.of ℤ_[ℓ] (levelCohomology T i n))
    (fun n => ModuleCat.ofHom (levelCohomologyTransitionₗ T i n))
private def limitCohomologyCone {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ) :
    Cone (cohomologyDiagram T i) where
  pt := ModuleCat.of ℤ_[ℓ] (limitCohomology T i)
  π := NatTrans.ofOpSequence (fun n => ModuleCat.ofHom (limitCohomologyProjection T i n))
    (by
      intro n
      simp only [Functor.const_obj_map, cohomologyDiagram,
        Functor.ofOpSequence_map_homOfLE_succ]
      ext x
      exact (x.2 n).symm)
private def limitCohomologyConeIsLimit {ℓ : ℕ} [Fact ℓ.Prime]
    (T : PerfectTower.{v} ℓ) (i : ℤ) : IsLimit (limitCohomologyCone T i) where
  lift s := ModuleCat.ofHom
    { toFun := fun x => ⟨fun n => (s.π.app ⟨n⟩).hom x, by
        intro n
        have h := congrArg (fun f => f.hom x) (s.w (homOfLE (Nat.le_succ n)).op)
        simp only [cohomologyDiagram, Functor.ofOpSequence_map_homOfLE_succ] at h
        exact h⟩
      map_add' x y := by ext n; exact map_add _ _ _
      map_smul' r x := by ext n; exact map_smul _ _ _ }
  fac s n := by ext x; rfl
  uniq s m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    exact congrArg (fun f => f.hom x) (h ⟨n⟩)

private def cohomologyDiagramIso {ℓ : ℕ} [Fact ℓ.Prime]
    (T : PerfectTower.{v} ℓ) (i : ℤ) :
    restrictedTower T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i ≅
      cohomologyDiagram T i := by
  let e (n : ℕ) := restrictedHomologyIso T i n
  let η : restrictedTower T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i ⟶
      cohomologyDiagram T i := NatTrans.ofOpSequence (fun n => (e n).hom) (by
    intro n
    simp only [Functor.comp_map, restrictedTower, cohomologyDiagram,
      Functor.ofOpSequence_map_homOfLE_succ]
    -- `simp` rewrote the transition but left the objects it sits between spelled
    -- `(Functor.ofOpSequence _).obj (op _)`; naming them `restrictedTowerObj` is what lets the
    -- rewrites below see the composite they are aimed at.
    change (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map
        (restrictedTowerTransition T n) ≫ (e n).hom =
      (e (n + 1)).hom ≫ ModuleCat.ofHom (levelCohomologyTransitionₗ T i n)
    dsimp only [restrictedTowerTransition]
    rw [Functor.map_comp, Category.assoc]
    change (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map
      ((padicRestriction.{v} (ℓ := ℓ) (n + 1)).map (T.transition n)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map _ ≫
          (restrictHomologyIsoOfHom.{v} (PadicInt.toZModPow (n + 1)) i).hom.app (T.obj n) = _
    rw [restrictHomologyIsoOfHom_comp]
    have hn := (restrictHomologyIsoOfHom.{v} (PadicInt.toZModPow (n + 1 + 1)) i).hom.naturality
      (T.transition n)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    congr 1)
  exact NatIso.ofComponents (fun n => e n.unop) (fun f => η.naturality f)

/-! ### Part (2): the limit cohomology is a finite ℤ_[ℓ]-module -/

/-- **Stacks 03V4, part (2).** Each `Hⁱ_∞` is a finite `ℤ_[ℓ]`-module. -/
public theorem finite_limitCohomology {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ) :
    Module.Finite ℤ_[ℓ] (limitCohomology T i) := by
  obtain ⟨K, hperf, hK⟩ := exists_perfect_derivedLimit T
  have := finite_limit_homology_of_perfect_derivedLimit (restrictedTower T) K hperf hK i
  exact Module.Finite.equiv ((HasLimit.isoOfNatIso (cohomologyDiagramIso T i)) ≪≫
    (limit.isLimit (cohomologyDiagram T i)).conePointUniqueUpToIso
      (limitCohomologyConeIsLimit T i)).toLinearEquiv

end Stacks.InverseSystem

end
