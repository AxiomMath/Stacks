module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonAdicLimitExact

/-!
# The comparison map of Stacks 0EIV is the completion of a morphism near the formal locus

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, put `U = Spec(A) ∖ V(𝔞)` and let `G`, `F` be
coherent modules on `U`. The comparison map
`Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison` sends a germ of a morphism
`s : G|_W ⟶ F|_W` on a neighbourhood `W` of the formal locus `U ∩ V(I)` to a morphism
`G^∧ ⟶ F^∧` of coherent adic systems. It is defined as a composite of canonical
identifications — the comparison of Stacks 0EG2 for `SheafHom(G, F)`, a shift of the
ideal-power tower, the passage to global sections, and the identification of Stacks 0882 — so it
is not visible from the definition what it does to `s`. This file computes it: restricted to
`W`, its components are the completion of `s`.

## Main results

* `Stacks.Algebraization.completionProjection_comp_completionInternalHomEquiv` — the components
  of the identification of Stacks 0882, on a compatible family of sections of the completion of
  `SheafHom(G, F)`: composed with the projection of `G`, the `n`-th component is the morphism read
  off the image of the `n`-th section under the level-`n` comparison.
* `Stacks.Algebraization.restrict_internalHomSectionsTopEquiv` and
  `Stacks.Algebraization.internalHomRestrictEquiv_map` — the morphism read off a global section of
  `SheafHom(G, M)` restricts to the morphism read off the restricted section, and reading off
  sections over an open is natural in the target.
* `Stacks.Algebraization.restrict_completionProjection_comp_nbhdHomComparison` — **the
  characterization**: for a section `s` of `SheafHom(G, F)` over `W ∈ 𝒱` and every `n`, the
  restriction to `W` of `G ⟶ G / I^(n+1) G ⟶ F / I^(n+1) F`, the second map being the `n`-th
  component of the comparison of `[s]`, is `s` followed by the restriction of
  `F ⟶ F / I^(n+1) F`.

## References

* [Stacks Project, Tag 0EIV](https://stacks.math.columbia.edu/tag/0EIV)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.Algebraization.NeighbourhoodHoms

/-- Applying both sides of an equation `f ≫ g = h` of morphisms of a concrete category to `x`. -/
private theorem apply_comp_eq_of_comp_eq {C : Type*} [Category* C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (H : f ≫ g = h) (x : ToType X) :
    g (f x) = h x :=
  (ConcreteCategory.comp_apply f g x).symm.trans (ConcreteCategory.congr_hom H x)

section
variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The components of the identification of Stacks 0882.** For a compatible family `y` of
global sections of the completion of `SheafHom(G, F)`, the `n`-th component of the corresponding
morphism `G^∧ ⟶ F^∧`, composed with the projection `G ⟶ G / I^(n+1) G`, is the morphism
`G ⟶ F / I^(n+1) F` read off the image of the `n`-th section of `y` under the level-`n`
comparison `SheafHom(G, F) / I^(n+1) ⟶ SheafHom(G, F / I^(n+1) F)`. -/
theorem completionProjection_comp_completionInternalHomEquiv
    (y : ToType (limit (C := ModuleCat.{u} Γ(X, ⊤)) (Stacks.Coherent.globalSectionsSystem
      ((completionFunctor X I).obj (internalHomCoherent X G F))))) (n : ℕ) :
    completionProjection X I G n ≫ (completionInternalHomEquiv X I G F y).hom.app (op n) =
      internalHomSectionsTopEquiv (coherentObj G) (((completionFunctor X I).obj F).obj.obj (op n))
        ((completedSheafHomStageMap G F n).val.app (op ⊤)
          (limit.π (C := ModuleCat.{u} Γ(X, ⊤)) (Stacks.Coherent.globalSectionsSystem
            ((completionFunctor X I).obj (internalHomCoherent X G F))) (op n) y)) := by
  set e := IsLimit.conePointUniqueUpToIso
        (@isLimitOfPreserves _ _ _ _ _ _ _
          (_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
          (limit.cone ((completionFunctor X I).obj (internalHomCoherent X G F)).obj)
          (limit.isLimit ((completionFunctor X I).obj (internalHomCoherent X G F)).obj)
          (_root_.SheafOfModules.evaluationPreservesLimit _ (op ⊤)))
        (limit.isLimit (Stacks.Coherent.globalSectionsSystem
          ((completionFunctor X I).obj (internalHomCoherent X G F)))) with he
  set z := ConcreteCategory.hom e.inv y with hz
  have hzn : ((limit.π ((completionFunctor X I).obj (internalHomCoherent X G F)).obj
        (op n)).val.app (op ⊤)) z =
      limit.π (C := ModuleCat.{u} Γ(X, ⊤)) (Stacks.Coherent.globalSectionsSystem
        ((completionFunctor X I).obj (internalHomCoherent X G F))) (op n) y := by
    have := IsLimit.conePointUniqueUpToIso_inv_comp
      (@isLimitOfPreserves _ _ _ _ _ _ _
          (_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
          (limit.cone ((completionFunctor X I).obj (internalHomCoherent X G F)).obj)
          (limit.isLimit ((completionFunctor X I).obj (internalHomCoherent X G F)).obj)
          (_root_.SheafOfModules.evaluationPreservesLimit _ (op ⊤)))
        (limit.isLimit (Stacks.Coherent.globalSectionsSystem
          ((completionFunctor X I).obj (internalHomCoherent X G F)))) (op n)
    exact congrArg (fun f => ModuleCat.Hom.hom f y) this
  set k := internalHomSectionsTopEquiv (coherentObj G)
      (limit (C := X.Modules) ((completionFunctor X I).obj F).obj)
      ((completedSheafHomComparison (I := I) G F).val.app (op ⊤) z) with hk
  have hE : completionInternalHomEquiv X I G F y =
      completionHomLimitEquiv (I := I) G ((completionFunctor X I).obj F) k := rfl
  rw [hE]
  refine (completionProjection_homToAdicSystem G ((completionFunctor X I).obj F) k (op n)).trans ?_
  rw [hk, ← internalHomSectionsTopEquiv_map, ← hzn]
  congr 1
  exact apply_comp_eq_of_comp_eq
    (congrArg (fun φ => φ.val.app (op ⊤)) (completedSheafHomComparison_π (I := I) G F (op n))) z

omit [IsLocallyNoetherian X] in
/-- Restricting the morphism read off a global section of `SheafHom(G, M)` to an open `W` gives
the morphism read off the restriction of the section to `W`. -/
theorem restrict_internalHomSectionsTopEquiv (M : X.Modules) (W : X.Opens)
    (σ : ((sheafHomFunctor X (coherentObj G)).obj M).val.obj (op ⊤)) :
    (Scheme.Modules.restrictFunctor W.ι).map (internalHomSectionsTopEquiv (coherentObj G) M σ) =
      internalHomRestrictEquiv (coherentObj G) M W
        (((sheafHomFunctor X (coherentObj G)).obj M).val.map (homOfLE (le_top (a := W))).op σ) := by
  conv_rhs => rw [← (internalHomSectionsTopMapAddEquiv (coherentObj G) M).apply_symm_apply σ]
  ext O x
  rfl

omit [IsLocallyNoetherian X] in
/-- Reading a section of `SheafHom(G, -)` over `W` as a morphism `G|_W ⟶ -|_W` is natural in the
target. -/
theorem internalHomRestrictEquiv_map {M N : X.Modules} (f : M ⟶ N) (W : X.Opens)
    (s : ((sheafHomFunctor X (coherentObj G)).obj M).val.obj (op W)) :
    internalHomRestrictEquiv (coherentObj G) N W
        (((sheafHomFunctor X (coherentObj G)).map f).val.app (op W) s) =
      internalHomRestrictEquiv (coherentObj G) M W s ≫
        (Scheme.Modules.restrictFunctor W.ι).map f := by
  ext O x
  rfl
end

section
variable {X : Scheme.{u}} [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- The inverse of `sectionsAbLimitIso` is compatible with the limit projections. -/
theorem sectionsAbLimitIso_inv_π (D : ℕᵒᵖ ⥤ X.Modules) (m : ℕᵒᵖ) :
    (sectionsAbLimitIso D).inv ≫ (sectionsAb X).map (limit.π D m) =
      limit.π (D ⋙ sectionsAb X) m := by
  rw [Iso.inv_comp_eq, sectionsAbLimitIso_hom_π]
end

section
variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules
    (complementZeroLocus A a : Scheme).ringCatSheaf)

/-- **The family of sections `nbhdHomComparison` feeds into Stacks 0882.** The `n`-th section of
the completion of `SheafHom(G, F)` attached to a formal section `c` of `SheafHom(G, F)` is the
`(n+1)`-st component of `c`, through the identification of the terms of the completion with the
ideal-power quotients. -/
theorem nbhdHomComparison_component
    (c : ToType (limit (formalSections A I a (internalHomNear A a G F).obj))) (n : ℕ) :
    limit.π (C := ModuleCat.{u} Γ((complementZeroLocus A a : Scheme), ⊤))
        (Stacks.Coherent.globalSectionsSystem
          ((completionFunctor (complementZeroLocus A a : Scheme)
            (idealSheafNearVanishing A I a)).obj (internalHomNear A a G F))) (op n)
      (ConcreteCategory.hom (globalSectionsLimitIso (idealSheafNearVanishing A I a)
        (internalHomNear A a G F)).hom
        (ConcreteCategory.hom ((sectionsAb (complementZeroLocus A a : Scheme)).map
          (adicCompletionLimitIso (idealSheafNearVanishing A I a)
            (internalHomNear A a G F)).hom)
          (ConcreteCategory.hom (sectionsAbLimitIso
            (adicQuotientSystem (idealSheafNearVanishing A I a)
              (internalHomNear A a G F).obj)).inv c))) =
      ((towerIso (idealSheafNearVanishing A I a) (internalHomNear A a G F) n).inv.val.app
        (op ⊤)) (limit.π (formalSections A I a (internalHomNear A a G F).obj) (op (n + 1)) c) := by
  have h1 : (globalSectionsLimitIso (idealSheafNearVanishing A I a)
        (internalHomNear A a G F)).hom ≫
      limit.π (C := ModuleCat.{u} Γ((complementZeroLocus A a : Scheme), ⊤))
        (Stacks.Coherent.globalSectionsSystem
          ((completionFunctor (complementZeroLocus A a : Scheme)
            (idealSheafNearVanishing A I a)).obj (internalHomNear A a G F))) (op n) =
      (_root_.SheafOfModules.evaluation (complementZeroLocus A a : Scheme).ringCatSheaf
          (op (⊤ : (complementZeroLocus A a : Scheme).Opens))).map
        (limit.π (C := (complementZeroLocus A a : Scheme).Modules)
          ((completionFunctor (complementZeroLocus A a : Scheme)
            (idealSheafNearVanishing A I a)).obj (internalHomNear A a G F)).obj (op n)) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ (op n)
  have h2 : (adicCompletionLimitIso (idealSheafNearVanishing A I a)
        (internalHomNear A a G F)).hom ≫
      limit.π (C := (complementZeroLocus A a : Scheme).Modules)
        ((completionFunctor (complementZeroLocus A a : Scheme)
        (idealSheafNearVanishing A I a)).obj (internalHomNear A a G F)).obj (op n) =
      limit.π (C := (complementZeroLocus A a : Scheme).Modules)
        (adicQuotientSystem (idealSheafNearVanishing A I a)
          (internalHomNear A a G F).obj) (op (n + 1)) ≫
        (towerIso (idealSheafNearVanishing A I a) (internalHomNear A a G F) n).inv :=
    limit.lift_π _ _
  have h3 := sectionsAbLimitIso_inv_π
    (adicQuotientSystem (idealSheafNearVanishing A I a) (internalHomNear A a G F).obj)
    (op (n + 1))
  set E := _root_.SheafOfModules.evaluation (complementZeroLocus A a : Scheme).ringCatSheaf
    (op (⊤ : (complementZeroLocus A a : Scheme).Opens)) with hE
  set v := ConcreteCategory.hom (sectionsAbLimitIso
    (adicQuotientSystem (idealSheafNearVanishing A I a) (internalHomNear A a G F).obj)).inv c
  have e1 := apply_comp_eq_of_comp_eq h1 ((E.map (adicCompletionLimitIso
    (idealSheafNearVanishing A I a) (internalHomNear A a G F)).hom) v)
  have e2 := (apply_comp_eq_of_comp_eq ((E.map_comp _ _).symm.trans
    ((congrArg E.map h2).trans (E.map_comp _ _))) v).trans (ConcreteCategory.comp_apply _ _ _)
  exact e1.trans (e2.trans (congrArg _ (apply_comp_eq_of_comp_eq h3 c)))
end


section
variable {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- If a global section `t` of `SheafHom(G, F) / I^(n+1)` restricts on `W` to the reduction of a
section `s` of `SheafHom(G, F)`, then its image under the level-`n` comparison restricts on `W` to
`s` followed by the projection `F ⟶ F / I^(n+1) F`. -/
theorem stage_towerIso_restrict (W : X.Opens) (n : ℕ)
    (t : Γ((adicQuotientSystem J (internalHomCoherent X G F).obj).obj (op (n + 1)), ⊤))
    (s : Γ((internalHomCoherent X G F).obj, W))
    (ht : ((adicQuotientSystem J (internalHomCoherent X G F).obj).obj (op (n + 1))).presheaf.map
        (homOfLE (le_top (a := W))).op t =
      (adicProj J (internalHomCoherent X G F).obj (op (n + 1))).app W s) :
    ((sheafHomFunctor X (coherentObj G)).obj
        (((completionFunctor X J).obj F).obj.obj (op n))).presheaf.map
        (homOfLE (le_top (a := W))).op
      ((completedSheafHomStageMap G F n).app ⊤
        ((towerIso J (internalHomCoherent X G F) n).inv.app ⊤ t)) =
      ((sheafHomFunctor X (coherentObj G)).map (completionProjection X J F n)).app W s := by
  have n1 := NatTrans.naturality_apply (completedSheafHomStageMap G F n).mapPresheaf
    (homOfLE (le_top (a := W))).op ((towerIso J (internalHomCoherent X G F) n).inv.app ⊤ t)
  have n2 := NatTrans.naturality_apply (towerIso J (internalHomCoherent X G F) n).inv.mapPresheaf
    (homOfLE (le_top (a := W))).op t
  have n4 : adicProj J (internalHomCoherent X G F).obj (op (n + 1)) ≫
      (towerIso J (internalHomCoherent X G F) n).inv =
        completionProjection X J (internalHomCoherent X G F) n :=
    (Iso.comp_inv_eq _).2 (completionProjection_comp_towerIso _ _ n).symm
  have n6 : (completedSheafHomStageMap G F n).app W
      ((towerIso J (internalHomCoherent X G F) n).inv.app W
        ((adicProj J (internalHomCoherent X G F).obj (op (n + 1))).app W s)) =
      ((sheafHomFunctor X (coherentObj G)).map (completionProjection X J F n)).app W s := by
    have e : adicProj J (internalHomCoherent X G F).obj (op (n + 1)) ≫
        (towerIso J (internalHomCoherent X G F) n).inv ≫ completedSheafHomStageMap G F n =
        (sheafHomFunctor X (coherentObj G)).map (completionProjection X J F n) :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ completedSheafHomStageMap G F n) n4).trans
        (completionProjection_completedSheafHomStageMap G F n))
    exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.app W) e) s
  exact n1.symm.trans ((congrArg _ (n2.symm.trans (congrArg _ ht))).trans n6)
end

section
variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules
    (complementZeroLocus A a : Scheme).ringCatSheaf)

/-- **The comparison map of Stacks 0EIV, restricted to a neighbourhood.** For a section `s` of
`SheafHom(G, F)` over a neighbourhood `W` of the formal locus and every `n`, the restriction to
`W` of `G ⟶ G / I^(n+1) G ⟶ F / I^(n+1) F`, the second map being the `n`-th component of
`nbhdHomComparison [s]`, is the morphism `G|_W ⟶ F|_W` that `s` is, followed by the restriction of
the projection `F ⟶ F / I^(n+1) F`. So `nbhdHomComparison [s]` is the completion of `s`, read on
`W`. -/
theorem restrict_completionProjection_comp_nbhdHomComparison (W : OpensNearVanishing A I a)
    (s : ToType ((sectionsNearVanishing A I a (internalHomNear A a G F).obj).obj W)) (n : ℕ) :
    (Scheme.Modules.restrictFunctor W.openSet.ι).map
        (completionProjection _ (idealSheafNearVanishing A I a) G n ≫
          (nbhdHomComparison A I a G F (ConcreteCategory.hom
            (colimit.ι (sectionsNearVanishing A I a (internalHomNear A a G F).obj) W) s)).hom.app
            (op n)) =
      internalHomRestrictEquiv (coherentObj G) F.obj W.openSet s ≫
        (Scheme.Modules.restrictFunctor W.openSet.ι).map
          (completionProjection _ (idealSheafNearVanishing A I a) F n) := by
  have k1 := completionProjection_comp_completionInternalHomEquiv
    (idealSheafNearVanishing A I a) G F
    (ConcreteCategory.hom (globalSectionsLimitIso (idealSheafNearVanishing A I a)
        (internalHomNear A a G F)).hom
      (ConcreteCategory.hom ((sectionsAb (complementZeroLocus A a : Scheme)).map
        (adicCompletionLimitIso (idealSheafNearVanishing A I a) (internalHomNear A a G F)).hom)
        (ConcreteCategory.hom (sectionsAbLimitIso (adicQuotientSystem
            (idealSheafNearVanishing A I a) (internalHomNear A a G F).obj)).inv
          (ConcreteCategory.hom (comparisonMap A I a (internalHomNear A a G F).obj)
            (ConcreteCategory.hom
              (colimit.ι (sectionsNearVanishing A I a (internalHomNear A a G F).obj) W) s))))) n
  refine (congrArg (Scheme.Modules.restrictFunctor W.openSet.ι).map k1).trans ?_
  refine (restrict_internalHomSectionsTopEquiv G _ W.openSet _).trans ?_
  refine Eq.trans ?_ (internalHomRestrictEquiv_map G (completionProjection _
    (idealSheafNearVanishing A I a) F n) W.openSet s)
  congr 1
  rw [nbhdHomComparison_component]
  exact stage_towerIso_restrict (idealSheafNearVanishing A I a) G F W.openSet n _ s
    (ConcreteCategory.congr_hom
      (comparisonMap_restrict A I a (internalHomNear A a G F).obj W (n + 1)) s)

end

end Stacks.Algebraization

end
