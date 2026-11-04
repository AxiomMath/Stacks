module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTowerSystem
public import StacksFrontier.Homology.Perfect.PadicReductionHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicPerfectPairing

/-!
# The levels of a perfect tower are the reductions of its limit, up to bounded torsion

Let `T = (Kₙ)` be a tower of perfect complexes over `ℤ/ℓⁿ⁺¹` in the sense of
[Tag 03V4](https://stacks.math.columbia.edu/tag/03V4) and `Hⁱ_∞ = limₙ Hⁱ(Kₙ)`
(`Stacks.InverseSystem.limitCohomology`), with projections `πₙ : Hⁱ_∞ → Hⁱ(Kₙ)`. Then:

* the kernel of `πₙ` is `ℓⁿ⁺¹ Hⁱ_∞`;
* there is a `c` such that `ℓᶜ Hⁱ(Kₙ) ⊆ im πₙ` for every `n`.

The proof follows the proof of 03V4: the derived limit `K` of the tower restricted to `ℤ_ℓ` is a
perfect complex with `K ⊗ᴸ ℤ/ℓⁿ⁺¹ ≅ Kₙ` ([Tag 0CQG](https://stacks.math.columbia.edu/tag/0CQG)),
`Hⁱ(K)` maps onto `Hⁱ_∞` (Milnor sequence, Tag 07KY), and the universal coefficient sequence
`StacksDraft.Perfect.homologyMap_reduction` bounds the kernel and the cokernel of
`Hⁱ(K) → Hⁱ(Kₙ)`, the cokernel by the exponent of the torsion of the finite module `Hⁱ⁺¹(K)`.
These are the hypotheses on the levels under which compatible pairings at finite level give a
perfect pairing on `Hⁱ_∞ ⊗ ℚ_ℓ`
(`Stacks.EtaleCohomology.LAdicPairing.exists_isPerfPair_of_forall_zmodPow`).

The coefficient tower `ℤ/ℓⁿ⁺¹ → ℤ_ℓ`, the tower restricted to `ℤ_ℓ` and the identification of its
cohomology with the inverse system `n ↦ Hⁱ(Kₙ)` (which needs the compatibility of
`restrictHomologyIsoOfHom` with composites of ring maps) are built inside the proof.

## Main results

* `finite_homology_of_isPerfect_padic`: the cohomology of a perfect `ℤ_ℓ`-complex is finite.
* `exists_eq_pow_smul_of_limitCohomologyProjection_eq_zero_and_pow_smul_mem_range`: the two
  statements above about the projections `πₙ`.
* `exists_eq_pow_smul_of_limit_π_eq_zero_and_pow_smul_mem_range`: the same for an inverse system
  isomorphic to `n ↦ Hⁱ(Kₙ)`, such as `n ↦ Hⁱ_c(X_k̄, Fₙ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v

namespace Stacks.InverseSystem

attribute [local instance] HasDerivedCategory.standard

/-- The cohomology of a perfect `ℤ_ℓ`-complex is a finite `ℤ_ℓ`-module. -/
theorem finite_homology_of_isPerfect_padic {ℓ : ℕ} [Fact ℓ.Prime]
    (K : DerivedCategory (ModuleCat.{v} ℤ_[ℓ])) (hK : StacksDraft.Perfect.IsPerfect K) (i : ℤ) :
    Module.Finite ℤ_[ℓ] ((DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).obj K) := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨e⟩⟩ := hK
  have : Module.Finite ℤ_[ℓ] (P.X i) := hf i
  have : Module.Finite ℤ_[ℓ] (P.cycles i) :=
    Module.Finite.of_injective (P.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have : Module.Finite ℤ_[ℓ] (P.homology i) :=
    Module.Finite.of_surjective (P.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have : Module.Finite ℤ_[ℓ]
      ((HomologicalComplex.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) (.up ℤ) i).obj P) := by
    show Module.Finite ℤ_[ℓ] (P.homology i)
    infer_instance
  exact Module.Finite.equiv
    (((DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).mapIso e) ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P).symm.toLinearEquiv

section
attribute [local irreducible] ZMod

/-- **The levels of a perfect tower are the reductions of its limit, up to bounded torsion.**
For a tower of perfect complexes `T` and a degree `i`, the kernel of every projection
`πₙ : Hⁱ_∞ → Hⁱ(Kₙ)` is `ℓⁿ⁺¹ Hⁱ_∞`, and a single power `ℓᶜ` maps every `Hⁱ(Kₙ)` into the image
of `πₙ`. -/
theorem exists_eq_pow_smul_of_limitCohomologyProjection_eq_zero_and_pow_smul_mem_range
    {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ) :
    ∃ c : ℕ, ∀ n : ℕ,
      (∀ a : limitCohomology T i, limitCohomologyProjection T i n a = 0 →
        ∃ a' : limitCohomology T i, a = (ℓ ^ (n + 1)) • a') ∧
      ∀ y : levelCohomology T i n, ∃ a : limitCohomology T i,
        limitCohomologyProjection T i n a = (ℓ ^ c) • y := by
  /- **Step 1.** Cohomology commutes with restriction of scalars compatibly with composites of
  ring maps.  The local definitions below fix the spelling of the two ends of the isomorphisms
  they name: taking `.app` or `symm.app` of the natural isomorphisms directly leaves the ends
  spelled through `⋙`, and no `rw` can pass between the two spellings. -/
  have mapHomologyIso_comp : ∀ {C D E : Type (v + 1)} [Category.{v} C] [Category.{v} D]
      [Category.{v} E] [Abelian C] [Abelian D] [Abelian E]
      (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
      [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      [PreservesFiniteLimits G] [PreservesFiniteColimits G],
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
        (S.mapHomologyIso (F ⋙ G)).hom := by
    intro C D E _ _ _ _ _ _ S F G _ _ _ _ _ _
    let h₁ := (S.homologyData.left.map F).map G
    let h₂ := S.homologyData.left.map (F ⋙ G)
    let d : ShortComplex.LeftHomologyMapData (𝟙 (S.map (F ⋙ G))) h₁ h₂ :=
      { φK := 𝟙 _
        φH := 𝟙 _
        commi := by
          simp only [ShortComplex.map_comp, ShortComplex.map_X₂,
            ShortComplex.LeftHomologyData.map_i, Functor.comp_map, ShortComplex.id_τ₂, h₁, h₂]
          exact (Category.id_comp _).trans (Category.comp_id _).symm
        commf' := by
          simp only [ShortComplex.map_comp, ShortComplex.map_X₁,
            ShortComplex.LeftHomologyData.map_f', ShortComplex.id_τ₁, Functor.comp_map, h₂, h₁]
          exact (Category.comp_id _).trans (Category.id_comp _).symm
        commπ := by
          simp only [ShortComplex.map_comp, ShortComplex.LeftHomologyData.map_π, Functor.comp_map,
            h₁, h₂]
          exact (Category.comp_id _).trans (Category.id_comp _).symm }
    have hm : (S.mapHomologyIso (F ⋙ G)).hom = h₁.homologyIso.hom := by
      have h := d.homologyMap_comm
      simp only [ShortComplex.homologyMap_id, Category.id_comp] at h
      exact h.trans (Category.comp_id _)
    have iso_cancel {X Y Z : E} (α : X ≅ Y) (γ : Z ≅ Y) :
        (α ≪≫ γ.symm).hom ≫ γ.hom = α.hom := by simp
    rw [S.homologyData.left.map F |>.mapHomologyIso_eq G, hm]
    exact iso_cancel h₁.homologyIso (G.mapIso (S.mapHomologyIso F))
  -- `(DerivedCategory.homologyFunctorFactors _ i).symm.app P`, written applied on both ends.
  let homologyFactors : ∀ {R : Type} [CommRing R] (P : CochainComplex (ModuleCat.{v} R) ℤ)
      (i : ℤ), P.homology i ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj (DerivedCategory.Q.obj P) :=
    fun P i => (DerivedCategory.homologyFunctorFactors _ i).symm.app P
  -- `ShortComplex.mapHomologyIso` for the degree-`i` short complex, both ends `homology`.
  let mapHomologyFactors : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
      (P : CochainComplex (ModuleCat.{v} S) ℤ) (i : ℤ),
      (((ModuleCat.restrictScalars.{v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        P).homology i ≅ (ModuleCat.restrictScalars.{v} f).obj (P.homology i) :=
    fun f P i => (P.sc i).mapHomologyIso (ModuleCat.restrictScalars.{v} f)
  -- `Functor.mapDerivedCategoryFactors` at one object, written applied on both ends.
  let restrictDerivedFactors : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
      (P : CochainComplex (ModuleCat.{v} S) ℤ),
      (ModuleCat.restrictScalars.{v} f).mapDerivedCategory.obj (DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars.{v} f).mapHomologicalComplex (.up ℤ)).obj P) :=
    fun f P => (ModuleCat.restrictScalars.{v} f).mapDerivedCategoryFactors.app P
  -- `ModuleCat.restrictScalarsComp'` at one object, written applied on both ends.
  let restrictScalarsCompApp : ∀ {R S A : Type} [CommRing R] [CommRing S] [CommRing A]
      (f : R →+* S) (g : S →+* A) (M : ModuleCat.{v} A),
      (ModuleCat.restrictScalars.{v} f).obj ((ModuleCat.restrictScalars.{v} g).obj M) ⟶
        (ModuleCat.restrictScalars.{v} (g.comp f)).obj M :=
    fun f g M => (ModuleCat.restrictScalarsComp'.{v} f g (g.comp f) rfl).inv.app M
  -- `restrictHomologyIsoOfHom` at one object, written applied on both ends.
  let restrictHomologyApp : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : ℤ)
      (K : DerivedCategory (ModuleCat.{v} S)),
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
          ((ModuleCat.restrictScalars.{v} f).mapDerivedCategory.obj K) ⟶
        (ModuleCat.restrictScalars.{v} f).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} S) i).obj K) :=
    fun f i K => (restrictHomologyIsoOfHom.{v} f i).hom.app K
  have restrictHomologyIsoOfHom_hom_app_Q : ∀ {R S : Type} [CommRing R] [CommRing S]
      (f : R →+* S) (i : ℤ) (P : CochainComplex (ModuleCat.{v} S) ℤ),
      restrictHomologyApp f i (DerivedCategory.Q.obj P) =
        (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
          (restrictDerivedFactors f P).hom ≫
        (homologyFactors
          (((ModuleCat.restrictScalars.{v} f).mapHomologicalComplex (.up ℤ)).obj P) i).inv ≫
        (mapHomologyFactors f P i).hom ≫
        (ModuleCat.restrictScalars.{v} f).map (homologyFactors P i).hom := by
    intro R S _ _ f i P
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
  have restrictHomologyIsoOfHom_comp_Q : ∀ {R S A : Type} [CommRing R] [CommRing S]
      [CommRing A] (f : R →+* S) (g : S →+* A) (i : ℤ)
      (P : CochainComplex (ModuleCat.{v} A) ℤ),
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
          ((StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, v}
            f g (g.comp f) rfl).hom.app (DerivedCategory.Q.obj P)) ≫
        restrictHomologyApp (g.comp f) i (DerivedCategory.Q.obj P) =
      restrictHomologyApp f i
          ((ModuleCat.restrictScalars.{v} g).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        (ModuleCat.restrictScalars.{v} f).map
          (restrictHomologyApp g i (DerivedCategory.Q.obj P)) ≫
        restrictScalarsCompApp f g
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
            (DerivedCategory.Q.obj P)) := by
    intro R S A _ _ _ f g i P
    let e := Functor.mapHomologicalComplexCompIso
      (ModuleCat.restrictScalarsComp'.{v} f g (g.comp f) rfl).symm (.up ℤ)
    have he : (restrictDerivedFactors f
          (((ModuleCat.restrictScalars.{v} g).mapHomologicalComplex (.up ℤ)).obj P)).inv ≫
        (ModuleCat.restrictScalars.{v} f).mapDerivedCategory.map
            (restrictDerivedFactors g P).inv ≫
          (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, v}
            f g (g.comp f) rfl).hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map (e.hom.app P) ≫
          (restrictDerivedFactors (g.comp f) P).inv := by
      simp [StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp, e,
        restrictDerivedFactors, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
    -- The `Epi` instance is given as that of an isomorphism: searching for it gets stuck on
    -- the universe of the limits `ModuleCat R` would need.
    have hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        ((restrictDerivedFactors f
          (((ModuleCat.restrictScalars.{v} g).mapHomologicalComplex (.up ℤ)).obj P)).inv ≫
        (ModuleCat.restrictScalars.{v} f).mapDerivedCategory.map
          (restrictDerivedFactors g P).inv)) :=
      inferInstanceAs (Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso
        ((restrictDerivedFactors f
          (((ModuleCat.restrictScalars.{v} g).mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
        (ModuleCat.restrictScalars.{v} f).mapDerivedCategory.mapIso
          (restrictDerivedFactors g P).symm)).hom)
    refine (cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
      ((restrictDerivedFactors f
          (((ModuleCat.restrictScalars.{v} g).mapHomologicalComplex (.up ℤ)).obj P)).inv ≫
        (ModuleCat.restrictScalars.{v} f).mapDerivedCategory.map
          (restrictDerivedFactors g P).inv))).mp ?_
    dsimp only [Functor.comp_obj]
    rw [← Functor.map_comp_assoc, Category.assoc, he]
    rw [Functor.map_comp, Category.assoc]
    rw [restrictHomologyIsoOfHom_hom_app_Q]
    simp only [Functor.map_comp, Category.assoc, Functor.comp_obj]
    rw [Iso.map_inv_hom_id_assoc]
    have hn : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
          ((ModuleCat.restrictScalars.{v} f).mapDerivedCategory.map
            (restrictDerivedFactors g P).inv) ≫
        restrictHomologyApp f i
          ((ModuleCat.restrictScalars.{v} g).mapDerivedCategory.obj
            (DerivedCategory.Q.obj P)) =
        restrictHomologyApp f i (DerivedCategory.Q.obj
            (((ModuleCat.restrictScalars.{v} g).mapHomologicalComplex (.up ℤ)).obj P)) ≫
          (ModuleCat.restrictScalars.{v} f).map
            ((DerivedCategory.homologyFunctor (ModuleCat.{v} S) i).map
              (restrictDerivedFactors g P).inv) :=
      (restrictHomologyIsoOfHom.{v} f i).hom.naturality
        ((ModuleCat.restrictScalars.{v} g).mapDerivedCategoryFactors.inv.app P)
    rw [reassoc_of% hn]
    rw [restrictHomologyIsoOfHom_hom_app_Q, restrictHomologyIsoOfHom_hom_app_Q]
    simp only [Functor.map_comp, Category.assoc]
    rw [Iso.map_inv_hom_id_assoc]
    rw [← Functor.map_comp_assoc _ ((DerivedCategory.homologyFunctor (ModuleCat.{v} S) i).map
        (restrictDerivedFactors g P).inv)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} S) i).map
        (restrictDerivedFactors g P).hom),
      Iso.map_inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [Iso.map_hom_inv_id_assoc]
    have heid : e.hom.app P = 𝟙 _ := by ext j x; rfl
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
    rw [← mapHomologyIso_comp (P.sc i) (ModuleCat.restrictScalars.{v} g)
      (ModuleCat.restrictScalars.{v} f)]
    rfl
  have restrictHomologyIsoOfHom_comp : ∀ {R S A : Type} [CommRing R] [CommRing S] [CommRing A]
      (f : R →+* S) (g : S →+* A) (h : R →+* A) (w : h = g.comp f) (i : ℤ)
      (K : DerivedCategory (ModuleCat.{v} A)),
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
          ((StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, v}
            f g h w).hom.app K) ≫ (restrictHomologyIsoOfHom.{v} h i).hom.app K =
      (restrictHomologyIsoOfHom.{v} f i).hom.app
          ((ModuleCat.restrictScalars.{v} g).mapDerivedCategory.obj K) ≫
        (ModuleCat.restrictScalars.{v} f).map ((restrictHomologyIsoOfHom.{v} g i).hom.app K) ≫
        (ModuleCat.restrictScalarsComp'.{v} f g h w).inv.app
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K) := by
    intro R S A _ _ _ f g h w i K
    subst h
    let F := ModuleCat.restrictScalars.{v} g
    let G := ModuleCat.restrictScalars.{v} f
    let H := ModuleCat.restrictScalars.{v} (g.comp f)
    let HR := DerivedCategory.homologyFunctor (ModuleCat.{v} R) i
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
      have : Epi (((F.mapDerivedCategory ⋙ G.mapDerivedCategory) ⋙ HR).map e.hom) :=
        inferInstanceAs (Epi (((F.mapDerivedCategory ⋙ G.mapDerivedCategory) ⋙ HR).mapIso e).hom)
      apply (cancel_epi (((F.mapDerivedCategory ⋙ G.mapDerivedCategory) ⋙ HR).map e.hom)).mp
      rw [α.naturality, β.naturality, hQ P]
    simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp] using congrArg (fun η => η.app K) hab
  /- **Step 2.** The coefficient tower `ℤ/ℓⁿ⁺¹ℤ`, with limit `ℤ_[ℓ]`. -/
  have hnil (n : ℕ) : IsNilpotent (RingHom.ker (levelCast ℓ n)) := by
    refine ⟨2, le_antisymm ?_ bot_le⟩
    rw [pow_two]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    have hval (z : ZMod (ℓ ^ (n + 1 + 1)))
        (hz : z ∈ RingHom.ker (levelCast ℓ n)) : ℓ ^ (n + 1) ∣ z.val := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      have h : levelCast ℓ n z = 0 := hz
      rw [← ZMod.natCast_zmod_val z, map_natCast] at h
      exact h
    obtain ⟨a, ha⟩ := hval x hx
    obtain ⟨b, hb⟩ := hval y hy
    show x * y = 0
    rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, ← Nat.cast_mul]
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    rw [ha, hb]
    have hpow : ℓ ^ (n + 1 + 1) ∣ ℓ ^ (n + 1) * ℓ ^ (n + 1) := by
      rw [← pow_add]
      exact pow_dvd_pow ℓ (by omega)
    rw [mul_mul_mul_comm]
    exact hpow.trans (dvd_mul_right _ (a * b))
  let Acoef : ℕᵒᵖ ⥤ CommRingCat :=
    { obj := fun n => CommRingCat.of (ZMod (ℓ ^ (n.unop + 1)))
      map := fun f => CommRingCat.ofHom (ZMod.castHom
        (pow_dvd_pow ℓ (Nat.add_le_add_right (leOfHom f.unop) 1)) _)
      map_id := fun _ => by apply CommRingCat.hom_ext; exact Subsingleton.elim _ _
      map_comp := fun _ _ => by apply CommRingCat.hom_ext; exact Subsingleton.elim _ _ }
  let ccoef : Cone Acoef :=
    { pt := CommRingCat.of ℤ_[ℓ]
      π :=
        { app := fun n => CommRingCat.ofHom (PadicInt.toZModPow (n.unop + 1))
          naturality := by
            intro n m f
            ext x
            exact (PadicInt.cast_toZModPow (m.unop + 1) (n.unop + 1)
              (Nat.add_le_add_right (leOfHom f.unop) 1) x).symm } }
  have hccoef : IsLimit ccoef := by
    have : Subsingleton (ZMod (ℓ ^ 0)) := by
      simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
    let fs (s : Cone Acoef) : (n : ℕ) → s.pt →+* ZMod (ℓ ^ n)
      | 0 => (ZMod.castHom (pow_dvd_pow ℓ (Nat.zero_le 1)) _).comp (s.π.app (Opposite.op 0)).hom
      | n + 1 => (s.π.app (Opposite.op n)).hom
    have hf (s : Cone Acoef) (m n : ℕ) (h : m ≤ n) :
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
  /- **Step 3.** The tower restricted to `ℤ_[ℓ]` and its cohomology. -/
  -- `X` and `t` are spelled exactly as in the statement of Stacks 0CQG
  -- (`derivedLimit_isPerfect_and_baseChange_iso`), so that its distinguished triangle is ours.
  let X : ℕ → DerivedCategory (ModuleCat.{v} ccoef.pt) := fun n =>
    (ModuleCat.restrictScalars.{v} (ccoef.π.app (Opposite.op n)).hom).mapDerivedCategory.obj
      (T.obj n)
  let t : ∀ n, X (n + 1) ⟶ X n := fun n =>
    (ModuleCat.restrictScalars.{v} (ccoef.π.app (Opposite.op (n + 1))).hom).mapDerivedCategory.map
        (T.transition n) ≫
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp
        (ccoef.π.app (Opposite.op (n + 1))).hom (Acoef.map (homOfLE (Nat.le_succ n)).op).hom
        (ccoef.π.app (Opposite.op n)).hom
        (congrArg CommRingCat.Hom.hom (ccoef.w (homOfLE (Nat.le_succ n)).op)).symm).hom.app
        (T.obj n)
  let F := Functor.ofOpSequence t
  let e : ∀ n, (DerivedCategory.homologyFunctor (ModuleCat.{v} ccoef.pt) i).obj (X n) ≅
      ModuleCat.of ℤ_[ℓ] (levelCohomology T i n) := fun n =>
    (restrictHomologyIsoOfHom.{v} (PadicInt.toZModPow (p := ℓ) (n + 1)) i).app (T.obj n)
  let Ecoh : F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} ccoef.pt) i ≅
      levelCohomologySystem T i := by
    let η : F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} ccoef.pt) i ⟶
        levelCohomologySystem T i := NatTrans.ofOpSequence (fun n => (e n).hom) (by
      intro n
      simp only [Functor.comp_map, F, levelCohomologySystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      -- The square, restated with the ring maps spelled `PadicInt.toZModPow` and `levelCast`
      -- rather than as the components of the cone `ccoef`.
      show (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map
          ((ModuleCat.restrictScalars.{v}
            (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).mapDerivedCategory.map (T.transition n) ≫
          (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp
            (PadicInt.toZModPow (n + 1 + 1)) (levelCast ℓ n) (PadicInt.toZModPow (n + 1))
            (by
              ext x
              exact (PadicInt.cast_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _) x).symm)).hom.app
            (T.obj n)) ≫
          (restrictHomologyIsoOfHom.{v} (PadicInt.toZModPow (p := ℓ) (n + 1)) i).hom.app
            (T.obj n) =
        (restrictHomologyIsoOfHom.{v} (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) i).hom.app
            (T.obj (n + 1)) ≫ ModuleCat.ofHom (levelCohomologyTransitionₗ T i n)
      rw [Functor.map_comp, Category.assoc, restrictHomologyIsoOfHom_comp]
      have hn := (restrictHomologyIsoOfHom.{v} (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))
        i).hom.naturality (T.transition n)
      dsimp only [Functor.comp_map] at hn
      rw [reassoc_of% hn]
      congr 1)
    exact NatIso.ofComponents (fun n => e n.unop) (fun f => η.naturality f)
  /- **Step 4.** The derived limit, its perfectness and the universal coefficient sequence. -/
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} ℤ_[ℓ]) :=
    moduleCat_hasExactLimitsOfShape_discrete ℤ_[ℓ] ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} ℤ_[ℓ])) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨K, hKlim⟩ : ∃ K, Pretriangulated.IsDerivedLimit F K := by
    obtain ⟨K, p, δ, hK⟩ := Pretriangulated.exists_isDerivedLimit F
    exact ⟨K, p, δ, hK⟩
  obtain ⟨a, b, htri, hH⟩ := DerivedCategory.isDerivedLimit_homology_shortExact F K hKlim
  have htri' : Pretriangulated.Triangle.mk a (Pi.lift (fun n => Pi.π X n -
      Pi.π X (n + 1) ≫ t n)) b ∈ distTriang _ := by
    simp only [F, Functor.ofOpSequence_map_homOfLE_succ] at htri
    exact htri
  have hpb := StacksDraft.DerivedInverseLimit.derivedLimit_isPerfect_and_baseChange_iso
    Acoef ccoef hccoef T.obj T.transition
    (fun n => ZMod.castHom_surjective (pow_dvd_pow ℓ (Nat.le_succ (n + 1))))
    (fun n => StacksDraft.DerivedInverseLimit.isLocallyNilpotent_of_isNilpotent _ (hnil n))
    (Or.inl T.isPerfect) T.comparison_isIso K a b htri'
  obtain ⟨hKperf, hbc⟩ := hpb
  -- the torsion of `Hⁱ⁺¹(K)` has bounded exponent
  have := finite_homology_of_isPerfect_padic K hKperf (i + 1)
  obtain ⟨k, hk⟩ := Stacks.EtaleCohomology.LAdicPairing.exists_pow_smul_eq_zero_of_mem_torsion
    (p := ℓ) (M := (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) (i + 1)).obj K)
  refine ⟨k, fun n => ?_⟩
  obtain ⟨e₀, j, q, w, he₀, hj, hq, hs⟩ := hH i
  let E := limitIsoLimitCohomology T i Ecoh
  let Φ := q ≫ E.hom
  have hΦsurj : Function.Surjective Φ := by
    have hq' : Function.Surjective q := (ModuleCat.epi_iff_surjective q).mp hs.epi_g
    exact E.toLinearEquiv.surjective.comp hq'
  let g := a ≫ Pi.π X n
  have hΦπ : ∀ x, limitCohomologyProjection T i n (Φ x) =
      (e n).hom ((DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map g x) := by
    intro x
    have h1 := congrArg (fun φ => φ.hom (q x)) (limitIsoLimitCohomology_hom_π T i Ecoh n)
    have h2 := congrArg (fun φ => φ.hom x) (hq n)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1 h2
    show limitCohomologyProjection T i n (E.hom (q x)) = _
    refine h1.trans ?_
    rw [h2, show (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map g =
      (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map a ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map
          (Pi.π X n) from Functor.map_comp _ _ _]
    rfl
  have hc : ∀ z : (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) (i + 1)).obj K,
      (ℓ ^ (n + 1)) • z = 0 → (ℓ ^ k) • z = 0 := by
    intro z hz
    have hmem : z ∈ Submodule.torsion ℤ_[ℓ] _ := by
      refine ⟨⟨(ℓ : ℤ_[ℓ]) ^ (n + 1), ?_⟩, ?_⟩
      · exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2
          (Fact.out : ℓ.Prime).ne_zero))
      · show (ℓ : ℤ_[ℓ]) ^ (n + 1) • z = 0
        rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
        exact hz
    have := hk z hmem
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
    exact this
  obtain ⟨h₁, h₂⟩ := StacksDraft.Perfect.homologyMap_reduction (n + 1) K hKperf (T.obj n) g
    (hbc n) i (ℓ ^ k) hc
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨x₀, rfl⟩ := hΦsurj x
    rw [hΦπ] at hx
    have hx' : (DerivedCategory.homologyFunctor (ModuleCat.{v} ℤ_[ℓ]) i).map g x₀ = 0 := by
      have := congrArg (e n).inv hx
      simpa using this
    obtain ⟨x', rfl⟩ := h₁ x₀ hx'
    exact ⟨Φ x', map_nsmul Φ.hom _ x'⟩
  · obtain ⟨x, hx⟩ := h₂ ((e n).inv y)
    refine ⟨Φ x, ?_⟩
    rw [hΦπ, hx, map_nsmul, Iso.inv_hom_id_apply]

/-- **The tower facts for an inverse system isomorphic to `n ↦ Hⁱ(Kₙ)`.**  For an inverse system
`S` of `ℤ_[ℓ]`-modules with `S ≅ levelCohomologySystem T i`, the kernel of the projection
`lim S → S(n)` is `ℓⁿ⁺¹ lim S`, and one power `ℓᶜ` maps every `S(n)` into its image. -/
theorem exists_eq_pow_smul_of_limit_π_eq_zero_and_pow_smul_mem_range
    {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ) {S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]}
    (e : S ≅ levelCohomologySystem T i) :
    ∃ c : ℕ, ∀ n : ℕ,
      (∀ a : (limit S : ModuleCat.{v} ℤ_[ℓ]), (limit.π S (Opposite.op n)).hom a = 0 →
        ∃ a' : (limit S : ModuleCat.{v} ℤ_[ℓ]), a = (ℓ ^ (n + 1)) • a') ∧
      ∀ y : S.obj (Opposite.op n), ∃ a : (limit S : ModuleCat.{v} ℤ_[ℓ]),
        (limit.π S (Opposite.op n)).hom a = (ℓ ^ c) • y := by
  obtain ⟨c, hc⟩ :=
    exists_eq_pow_smul_of_limitCohomologyProjection_eq_zero_and_pow_smul_mem_range T i
  let L := limitLinearEquivLimitCohomology T i e
  have hL (n : ℕ) (a : (limit S : ModuleCat.{v} ℤ_[ℓ])) :
      limitCohomologyProjection T i n (L a) =
        (e.hom.app (Opposite.op n)).hom ((limit.π S (Opposite.op n)).hom a) :=
    congrArg (fun φ => φ.hom a) (limitIsoLimitCohomology_hom_π T i e n)
  refine ⟨c, fun n => ⟨fun a ha => ?_, fun y => ?_⟩⟩
  · obtain ⟨a', ha'⟩ := (hc n).1 (L a) (by rw [hL, ha]; exact map_zero _)
    refine ⟨L.symm a', ?_⟩
    rw [← map_nsmul L.symm, ← ha', LinearEquiv.symm_apply_apply]
  · obtain ⟨a', ha'⟩ := (hc n).2 ((e.hom.app (Opposite.op n)).hom y)
    refine ⟨L.symm a', (e.app (Opposite.op n)).toLinearEquiv.injective ?_⟩
    show (e.hom.app (Opposite.op n)).hom _ = (e.hom.app (Opposite.op n)).hom _
    rw [← hL, LinearEquiv.apply_symm_apply, ha', map_nsmul]
    rfl

end

end Stacks.InverseSystem

end
