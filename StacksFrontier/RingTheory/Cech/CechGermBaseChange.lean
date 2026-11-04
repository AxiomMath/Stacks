module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.RingTheory.Cech.CechColimitDatum
public import StacksFrontier.RingTheory.Cech.RingBaseChangeDerived

/-!
# Stacks 099D: the germ map of the colimit, and the transitivity of base change

This file reduces condition (c) of [Stacks, Tag 099D] — for an *arbitrary* pair `(A, I)` with `I`
finitely generated — to a single statement about the germ maps of the filtered colimit of step 2.

The germ map on complexes `Stacks.PairSite.germComplexMap` attaches to an object `X` of the index
category of step 2 the map of complexes of `X.pair.ring`-modules from the sections of a complex of
pair-modules at the presented pair `X.pair` to the colimit complex of step 2. By
`Stacks.PairSite.germComplexMap_eq` it is datum (3) of the tag at the ring map
`X.pair.ring → A` that the object `X` *is*, so the base-change statement about it is condition (c)
for the ring maps out of the presented pairs. That statement is
`Stacks.PairSite.GermBaseChange`; it is immediate when `(A, I)` is itself a presented pair
(`Stacks.PairSite.isIso_derivedBaseChange_germComplexMap_presented`), and it is proved in general
in `StacksFrontier/RingTheory/Cech/CechGermBaseChangeProof.lean`
(`Stacks.PairSite.germBaseChange`).

Granted it, condition (c) holds at every ring map: this is
`Stacks.PairSite.colimitBaseChange_of_germBaseChange`, and the engine is the transitivity of the
base-change comparison along a composite of ring maps,
`Stacks.LocalCohomology.derivedBaseChange_comp`, whose categorical content is the mate identity
`Stacks.LocalCohomology.homEquiv_symm_comp` for a composite of adjunctions.

## Main definitions

* `Stacks.PairSite.germComplexMap` — the germ map on complexes.
* `Stacks.PairSite.GermBaseChange` — the one base-change statement that is missing.
* `Stacks.LocalCohomology.extendScalarsCompComplexIso` — extension of scalars along a composite
  of ring maps, on cochain complexes.

## Main results

* `Stacks.LocalCohomology.homEquiv_symm_comp` — the adjoint of a composite is the composite of
  the adjoints, through the comparison isomorphism of the right adjoints and its mate.
* `Stacks.LocalCohomology.complexAdj_homEquiv_symm_comp` — that identity for extension and
  restriction of scalars on cochain complexes.
* `Stacks.LocalCohomology.derivedBaseChange_comp` — **the transitivity of the base-change
  comparison** of condition (c) along a composite of ring maps.
* `Stacks.PairSite.germ_eq_colimitSelfInv_comp` and `Stacks.PairSite.germComplexMap_eq` — the
  germ map at `X` is datum (3) of the colimit along the structure map of `X`, composed with the
  identification of the colimit at the presented pair `X.pair` with the sections there.
* `Stacks.PairSite.germComplexMap_augmentation` — **condition (a) at the germ map**, on the nose.
* `Stacks.PairSite.germComplexMap_transport` — the germ map at the transport of an object is the
  germ map followed by datum (3).
* `Stacks.PairSite.colimitBaseChange_of_germBaseChange` — **condition (c) of the tag for the
  colimit complex, at every ring map**, granted `Stacks.PairSite.GermBaseChange`.

## Implementation notes

No `@[stacks 099D]` attribute is attached: what is proved here is condition (c) for the complex
of step 2, which is one field of `Stacks.LocalCohomology.FunctorialCechData`. The unconditional
term the attribute sits on is `Stacks.LocalCohomology.nonempty_functorialCechData`. Condition (d)
at an arbitrary pair (`Stacks.PairSite.ColimitCechIso`) is `Stacks.PairSite.colimitCechIso`, in
`StacksFrontier/RingTheory/Cech/CechColimitCechIso.lean`, and step 3 is
`Stacks.PairSite.exists_presentedCechDatum`, in
`StacksFrontier/RingTheory/Cech/PairCechColimit.lean`.

Several steps are routed through small lemmas whose objects are *variables*
(`Stacks.LocalCohomology.comp_eq_of_comp_inv`, `Stacks.LocalCohomology.isIso_comp_aux`,
`Stacks.LocalCohomology.isIso_of_isIso_comp₂`, `Stacks.LocalCohomology.assoc_cancel_aux`). The
reason is that the comparison maps of derived extension of scalars have types spelled with
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral`, a `def` built by
tactics: a composite of two of them is type-correct only at default transparency, so `rw` and
`simp`, which re-check their motives at the implicit transparency level, fail outright. Applying a
lemma stated with variable objects moves the work to the elaborator, where the unfolding happens.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

/-! ### The mate of a composite of adjunctions -/

namespace Stacks.LocalCohomology

/-- **The adjoint of a composite, through a comparison of the right adjoints.** Let
`adj₁ : F₁ ⊣ G₁`, `adj₂ : F₂ ⊣ G₂` and `adj₃ : F₃ ⊣ G₃` be adjunctions, let
`τ : G₂ ⋙ G₁ ≅ G₃` compare the composite right adjoint with the third one, and let
`θ : F₃ ⟶ F₁ ⋙ F₂` be its mate, in the sense that `adj₃.homEquiv` carries `θ` to the unit of the
composite adjunction followed by `τ.hom`. Then the `adj₃`-adjoint of a composite
`u ≫ G₁.map v ≫ τ.hom` is the composite of the `adj₁`- and `adj₂`-adjoints, preceded by `θ`.

For extension and restriction of scalars the hypothesis `hθ` is
`ModuleCat.homEquiv_extendScalarsComp`, which holds because `ModuleCat.extendScalarsComp` is
*defined* as the mate of `ModuleCat.restrictScalarsComp`. This is the categorical input of the
transitivity of `Stacks.LocalCohomology.derivedBaseChange` along a composite of ring maps. -/
theorem homEquiv_symm_comp {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    {F₁ : C₁ ⥤ C₂} {G₁ : C₂ ⥤ C₁} {F₂ : C₂ ⥤ C₃} {G₂ : C₃ ⥤ C₂} {F₃ : C₁ ⥤ C₃} {G₃ : C₃ ⥤ C₁}
    (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) (adj₃ : F₃ ⊣ G₃) (τ : G₂ ⋙ G₁ ≅ G₃)
    {K : C₁} {L : C₂} {M : C₃} (θ : F₃.obj K ⟶ F₂.obj (F₁.obj K))
    (hθ : adj₃.homEquiv K (F₂.obj (F₁.obj K)) θ =
      adj₁.unit.app K ≫ G₁.map (adj₂.unit.app (F₁.obj K)) ≫
        τ.hom.app (F₂.obj (F₁.obj K)))
    (u : K ⟶ G₁.obj L) (v : L ⟶ G₂.obj M) :
    (adj₃.homEquiv K M).symm (u ≫ G₁.map v ≫ τ.hom.app M) =
      θ ≫ F₂.map ((adj₁.homEquiv K L).symm u) ≫ (adj₂.homEquiv L M).symm v := by
  have hunit : adj₁.unit.app K ≫ G₁.map (adj₂.unit.app (F₁.obj K)) ≫
        τ.hom.app (F₂.obj (F₁.obj K)) =
      (adj₁.comp adj₂).unit.app K ≫ τ.hom.app (F₂.obj (F₁.obj K)) := by
    rw [Adjunction.comp_unit_app, Category.assoc]
  have hstep : (adj₁.comp adj₂).homEquiv K M
      (F₂.map ((adj₁.homEquiv K L).symm u) ≫ (adj₂.homEquiv L M).symm v) =
      u ≫ G₁.map v := by
    rw [Adjunction.comp_homEquiv]
    rw [show ∀ (w : F₂.obj (F₁.obj K) ⟶ M),
        (Equiv.trans (adj₂.homEquiv (F₁.obj K) M) (adj₁.homEquiv K (G₂.obj M))) w =
          adj₁.homEquiv K (G₂.obj M) (adj₂.homEquiv (F₁.obj K) M w) from fun _ => rfl]
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  refine (Equiv.symm_apply_eq _).2 (Eq.symm ?_)
  rw [Adjunction.homEquiv_naturality_right, hθ, hunit, Category.assoc, ← τ.hom.naturality,
    ← Category.assoc, ← Adjunction.homEquiv_unit, hstep, Category.assoc]

/-! ### Two pieces of pure composition algebra

Both are stated with the objects as variables on purpose. The concrete morphisms they are applied
to below have types spelled with
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral`, which is a `def` built
by tactics, so composites of them are type-correct only at default
transparency; `rw` and `simp`, which re-check their motives at the implicit transparency level,
fail on such a goal. Applying a lemma whose objects are variables does the rewriting at the
elaborator's transparency instead. -/

/-- Cancel a right inverse out of a factorization: from `f ≫ g ≫ i = k` and `i ≫ j = 𝟙`,
conclude `f ≫ g = k ≫ j`. -/
theorem comp_eq_of_comp_inv {C : Type*} [Category C] {X Y Z T : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {i : Z ⟶ T} {j : T ⟶ Z} (hij : i ≫ j = 𝟙 Z) {k : X ⟶ T} (h : f ≫ g ≫ i = k) :
    f ≫ g = k ≫ j := by
  rw [← h, Category.assoc, Category.assoc, hij, Category.comp_id]

/-- A composite of two isomorphisms is an isomorphism, with the invertibility of the factors as
explicit arguments. Stated with the objects as variables, for the reason explained above. -/
theorem isIso_comp_aux {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIso f) (hg : IsIso g) : IsIso (f ≫ g) := by
  have := hf
  have := hg
  infer_instance

/-- Cancel two invertible left factors out of an invertible threefold composite. Stated with the
objects as variables, for the reason explained above. -/
theorem isIso_of_isIso_comp₂ {C : Type*} [Category C] {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (hf : IsIso f) (hg : IsIso g) (hfgh : IsIso (f ≫ g ≫ h)) : IsIso h := by
  have := hf
  have := hg
  have := hfgh
  have : IsIso (g ≫ h) := IsIso.of_isIso_comp_left f (g ≫ h)
  exact IsIso.of_isIso_comp_left g h

/-- The composition algebra of the transitivity of the base-change comparison: a naturality
square `hnat`, a factorization `hfac` and a cancellation `hHH` compose into one identity. -/
theorem assoc_cancel_aux {C : Type*} [Category C] {W X₀ X₁ X₂ X₃ X₄ Y V : C}
    {Hi : W ⟶ X₀} {H : X₀ ⟶ W} (hHH : Hi ≫ H = 𝟙 W)
    {m : X₀ ⟶ X₂} {Fcf : X₀ ⟶ X₁} {p : X₁ ⟶ X₂} (hm : m = Fcf ≫ p)
    {cL : X₂ ⟶ X₃} {cE : X₁ ⟶ X₄} {Ea : X₄ ⟶ X₃} (hnat : p ≫ cL = cE ≫ Ea)
    {c3 : W ⟶ Y} {tQ : Y ⟶ X₄} (hfac : Fcf ≫ cE = (H ≫ c3) ≫ tQ) (b : X₃ ⟶ V) :
    Hi ≫ m ≫ cL ≫ b = c3 ≫ tQ ≫ Ea ≫ b := by
  have h1 : p ≫ cL ≫ b = cE ≫ Ea ≫ b := by
    rw [← Category.assoc, hnat, Category.assoc]
  have h2 : Fcf ≫ cE ≫ Ea ≫ b = (H ≫ c3) ≫ tQ ≫ Ea ≫ b := by
    rw [← Category.assoc, hfac, Category.assoc]
  rw [hm, Category.assoc, h1, h2, Category.assoc H c3, ← Category.assoc Hi H, hHH,
    Category.id_comp]

/-! ### The mate identity for extension of scalars on complexes -/

section ExtendComp

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

open CochainComplex.DerivedExtensionScalars Stacks.CechRingBaseChange

/-- **Extension of scalars along a composite of ring maps, on cochain complexes.** This is
`ModuleCat.extendScalarsComp` applied in each degree; it is the mate of
`Stacks.LocalCohomology.restrictScalarsCompComplexIso` under the adjunctions
`Stacks.CechRingBaseChange.complexAdj`. -/
def extendScalarsCompComplexIso (φ : A →+* B) (ψ : B →+* C) :
    (ModuleCat.extendScalars.{u, u, u} (ψ.comp φ)).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} φ ψ) (ComplexShape.up ℤ)

/-- In degree `n`, the component of `extendScalarsCompComplexIso φ ψ` at `K` is the component of
`ModuleCat.extendScalarsComp φ ψ` at `K.X n`. -/
@[simp]
theorem extendScalarsCompComplexIso_hom_app_f (φ : A →+* B) (ψ : B →+* C)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ((extendScalarsCompComplexIso φ ψ).hom.app K).f n =
      (ModuleCat.extendScalarsComp.{u, u} φ ψ).hom.app (K.X n) := rfl

/-- **The adjoint of a composite, for extension and restriction of scalars on complexes.** The
complex-level adjoint of `u ≫ Res_φ(v)`, read through the comparison of the two restrictions of
scalars, is the composite of the adjoints of `u` and `v`, preceded by the comparison of the two
extensions of scalars. -/
theorem complexAdj_homEquiv_symm_comp (φ : A →+* B) (ψ : B →+* C)
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {L : CochainComplex (ModuleCat.{u} B) ℤ}
    {M : CochainComplex (ModuleCat.{u} C) ℤ}
    (u : K ⟶ (CochainComplex.restrictScalars φ).obj L)
    (v : L ⟶ (CochainComplex.restrictScalars ψ).obj M) :
    ((complexAdj (ψ.comp φ)).homEquiv K M).symm
        (u ≫ (CochainComplex.restrictScalars φ).map v ≫
          (restrictScalarsCompComplexIso φ ψ).hom.app M) =
      (extendScalarsCompComplexIso φ ψ).hom.app K ≫
        ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((complexAdj φ).homEquiv K L).symm u) ≫
          ((complexAdj ψ).homEquiv L M).symm v := by
  refine homEquiv_symm_comp (complexAdj φ) (complexAdj ψ) (complexAdj (ψ.comp φ))
    (restrictScalarsCompComplexIso φ ψ) ((extendScalarsCompComplexIso φ ψ).hom.app K) ?_ u v
  refine Eq.trans (Adjunction.homEquiv_unit _ _ _ _)
    (HomologicalComplex.hom_ext _ _ fun n => ?_)
  exact (Adjunction.homEquiv_unit (ModuleCat.extendRestrictScalarsAdj (ψ.comp φ)) _ _
      ((ModuleCat.extendScalarsComp.{u, u} φ ψ).hom.app (K.X n))).symm.trans
    (ModuleCat.homEquiv_extendScalarsComp.{u, u} φ ψ (K.X n))

/-! ### Transitivity of the base-change comparison -/

/-- The complex-level comparison of extension of scalars along a composite, read in the derived
category: it is the localization of
`Stacks.LocalCohomology.extendScalarsCompComplexIso`. -/
theorem extensionOfScalarsComplexComp_hom_app (φ : A →+* B) (ψ : B →+* C)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (extensionOfScalarsComplexComp φ ψ).hom.app K =
      DerivedCategory.Q.map ((extendScalarsCompComplexIso φ ψ).hom.app K) := rfl

/-- **Transitivity of the base-change comparison of condition (c) of [Stacks, Tag 099D].** For
ring maps `φ : A → B` and `ψ : B → C`, a map `u : K → Res_φ L` of complexes of `A`-modules and a
map `v : L → Res_ψ M` of complexes of `B`-modules, the comparison attached to the composite
`u ≫ Res_φ(v)` along `ψ ∘ φ` is the comparison of `u` base-changed to `C`, followed by the
comparison of `v`, through the composition isomorphism of derived extension of scalars.

In particular, if two of the three base-change comparisons are isomorphisms then so is the third;
that is how condition (c) for a general ring map is deduced from condition (c) for the ring maps
out of the presented pairs. -/
theorem derivedBaseChange_comp (φ : A →+* B) (ψ : B →+* C)
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {L : CochainComplex (ModuleCat.{u} B) ℤ}
    {M : CochainComplex (ModuleCat.{u} C) ℤ}
    (u : K ⟶ (CochainComplex.restrictScalars φ).obj L)
    (v : L ⟶ (CochainComplex.restrictScalars ψ).obj M) :
    derivedBaseChange (ψ.comp φ)
        (u ≫ (CochainComplex.restrictScalars φ).map v ≫
          (restrictScalarsCompComplexIso φ ψ).hom.app M) =
      (totalDerivedExtensionScalarsComp φ ψ).inv.app (DerivedCategory.Q.obj K) ≫
        (derivedExtensionScalarsGeneral.{u, u, u} ψ).functor.map (derivedBaseChange φ u) ≫
          derivedBaseChange ψ v := by
  have hHH : (totalDerivedExtensionScalarsComp φ ψ).inv.app (DerivedCategory.Q.obj K) ≫
      (totalDerivedExtensionScalarsComp φ ψ).hom.app (DerivedCategory.Q.obj K) = 𝟙 _ :=
    Iso.inv_hom_id_app _ _
  have hnat : (derivedExtension ψ).functor.map
          (DerivedCategory.Q.map (((complexAdj φ).homEquiv K L).symm u)) ≫
        (derivedExtension ψ).comparison.app L =
      (derivedExtension ψ).comparison.app
          (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (((complexAdj φ).homEquiv K L).symm u)) :=
    (derivedExtension ψ).comparison.naturality (((complexAdj φ).homEquiv K L).symm u)
  have hinv : DerivedCategory.Q.map ((extendScalarsCompComplexIso φ ψ).inv.app K) ≫
      DerivedCategory.Q.map ((extendScalarsCompComplexIso φ ψ).hom.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hcmp : (derivedExtension ψ).functor.map ((derivedExtension φ).comparison.app K) ≫
        ((derivedExtension ψ).comparison.app
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((extendScalarsCompComplexIso φ ψ).inv.app K)) =
      (totalDerivedExtensionScalarsComp φ ψ).hom.app (DerivedCategory.Q.obj K) ≫
        (derivedExtension (ψ.comp φ)).comparison.app K :=
    totalDerivedExtensionScalarsComp_comparison φ ψ K
  have hmc : (derivedExtension ψ).functor.map ((derivedExtension φ).comparison.app K ≫
        DerivedCategory.Q.map (((complexAdj φ).homEquiv K L).symm u)) =
      (derivedExtension ψ).functor.map ((derivedExtension φ).comparison.app K) ≫
        (derivedExtension ψ).functor.map
          (DerivedCategory.Q.map (((complexAdj φ).homEquiv K L).symm u)) :=
    Functor.map_comp _ _ _
  have hadj : DerivedCategory.Q.map (((complexAdj (ψ.comp φ)).homEquiv K M).symm
        (u ≫ (CochainComplex.restrictScalars φ).map v ≫
          (restrictScalarsCompComplexIso φ ψ).hom.app M)) =
      DerivedCategory.Q.map ((extendScalarsCompComplexIso φ ψ).hom.app K) ≫
        DerivedCategory.Q.map (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (((complexAdj φ).homEquiv K L).symm u)) ≫
          DerivedCategory.Q.map (((complexAdj ψ).homEquiv L M).symm v) := by
    rw [complexAdj_homEquiv_symm_comp φ ψ u v, Functor.map_comp, Functor.map_comp]
  have hd₃ : derivedBaseChange (ψ.comp φ)
        (u ≫ (CochainComplex.restrictScalars φ).map v ≫
          (restrictScalarsCompComplexIso φ ψ).hom.app M) =
      (derivedExtension (ψ.comp φ)).comparison.app K ≫
        DerivedCategory.Q.map (((complexAdj (ψ.comp φ)).homEquiv K M).symm
          (u ≫ (CochainComplex.restrictScalars φ).map v ≫
            (restrictScalarsCompComplexIso φ ψ).hom.app M)) :=
    derivedBaseChange_eq _ _
  have hd₁ : derivedBaseChange φ u = (derivedExtension φ).comparison.app K ≫
      DerivedCategory.Q.map (((complexAdj φ).homEquiv K L).symm u) :=
    derivedBaseChange_eq _ _
  have hd₂ : derivedBaseChange ψ v = (derivedExtension ψ).comparison.app L ≫
      DerivedCategory.Q.map (((complexAdj ψ).homEquiv L M).symm v) :=
    derivedBaseChange_eq _ _
  have hRHS : (totalDerivedExtensionScalarsComp φ ψ).inv.app (DerivedCategory.Q.obj K) ≫
        (derivedExtension ψ).functor.map (derivedBaseChange φ u) ≫ derivedBaseChange ψ v =
      (totalDerivedExtensionScalarsComp φ ψ).inv.app (DerivedCategory.Q.obj K) ≫
        (derivedExtension ψ).functor.map ((derivedExtension φ).comparison.app K ≫
            DerivedCategory.Q.map (((complexAdj φ).homEquiv K L).symm u)) ≫
          ((derivedExtension ψ).comparison.app L ≫
            DerivedCategory.Q.map (((complexAdj ψ).homEquiv L M).symm v)) := by
    rw [hd₁, hd₂]
    rfl
  exact (hd₃.trans (congrArg (fun t => (derivedExtension (ψ.comp φ)).comparison.app K ≫ t)
    hadj)).trans ((assoc_cancel_aux hHH hmc hnat (comp_eq_of_comp_inv hinv hcmp)
      (DerivedCategory.Q.map (((complexAdj ψ).homEquiv L M).symm v))).symm.trans hRHS.symm)

end ExtendComp

end Stacks.LocalCohomology

namespace Stacks.PairSite

variable {A B : Type u} [CommRing A] [CommRing B]
variable {I : Ideal A} {J : Ideal B}

open PairOver

/-! ### The germ map on complexes -/

/-- **The germ map on complexes.** For an object `X` of the index category of step 2 of
[Stacks, Tag 099D] this is the map of complexes of `X.pair.ring`-modules from the sections of a
complex of pair-modules at the presented pair `X.pair` to the colimit complex of step 2, the
latter read over `X.pair.ring` along the structure map of `X`. Degreewise it is
`Stacks.PairSite.PairOver.germ`, and its commutation with the differentials is
`Stacks.PairSite.PairOver.germAt_naturality`. -/
def germComplexMap (hI : I.FG) (K : CochainComplex PairModule.{u} ℤ) (X : PairOver A I) :
    sectionsComplex K X.pair ⟶
      (CochainComplex.restrictScalars X.hom).obj ((colimitComplexFunctor hI).obj K) where
  f n := germ hI (K.X n) X
  comm' n m _ := ModuleCat.hom_ext (LinearMap.ext fun x =>
    germAt_naturality hI (K.d n m) X x)

/-- In degree `n`, `germComplexMap hI K X` is the germ map `germ hI (K.X n) X`. -/
@[simp]
theorem germComplexMap_f (hI : I.FG) (K : CochainComplex PairModule.{u} ℤ) (X : PairOver A I)
    (n : ℤ) : (germComplexMap hI K X).f n = germ hI (K.X n) X := rfl

/-- **An object of the index category is the transport of the terminal object of the index
category of its own pair.** The transport along the structure map of `X`
(`Stacks.PairSite.PairOver.transport`) carries `Stacks.PairSite.PairOver.self X.pair` to `X`, on
the nose: the transport composes the structure map with the identity. -/
theorem transport_obj_self (X : PairOver A I) :
    (transport X.hom X.map_ideal.symm).obj (self X.pair) = X := rfl

/-- **The germ map is datum (3) of the colimit along the structure map of `X`.** The germ at `X`
of a pair-module is the germ at the terminal object of the index category of `X.pair`, followed by
the comparison map of datum (3) for the ring map `X.pair.ring → A`. -/
theorem germ_eq_colimitSelfInv_comp (hI : I.FG) (M : PairModule.{u}) (X : PairOver A I) :
    germ hI M X =
      colimitSelfInv X.pair M ≫ colimitMap X.hom X.pair.ideal_fg hI X.map_ideal.symm M :=
  ModuleCat.hom_ext (LinearMap.ext fun m =>
    (colimitMap_germAt X.hom X.pair.ideal_fg hI X.map_ideal.symm M (self X.pair) m).symm)

/-- **The germ map on complexes is datum (3) of the colimit along the structure map of `X`.**
Under the identification `Stacks.PairSite.PairOver.colimitComplexSelfIso` of the colimit complex
at a presented pair with the complex of sections there, the germ map at `X` *is*
`Stacks.PairSite.PairOver.colimitComplexMap` along the structure map of `X`. So the base-change
statement about the germ map is condition (c) of [Stacks, Tag 099D] for the ring map
`X.pair.ring → A`, and conversely. -/
theorem germComplexMap_eq (hI : I.FG) (K : CochainComplex PairModule.{u} ℤ)
    (X : PairOver A I) :
    germComplexMap hI K X =
      (colimitComplexSelfIso X.pair K).inv ≫
        colimitComplexMap X.hom X.pair.ideal_fg hI X.map_ideal.symm K := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.comp_f, germComplexMap_f]
  exact germ_eq_colimitSelfInv_comp hI (K.X n) X

/-- **Condition (a) of [Stacks, Tag 099D] at the germ map, on the nose.** The germ map is
compatible with the augmentation of datum (2) at the presented pair `X.pair` and with the
augmentation of the colimit at `(A, I)`. This is the transport of
`Stacks.PairSite.PairOver.colimitComplexMap_augmentation` along
`Stacks.PairSite.germComplexMap_eq`, the two augmentations being matched by
`Stacks.PairSite.PairOver.colimitAugmentation_self`. -/
theorem germComplexMap_augmentation (hI : I.FG) {K : CochainComplex PairModule.{u} ℤ}
    (α : K ⟶ structureSingle.{u}) (X : PairOver A I) :
    germComplexMap hI K X ≫
        (CochainComplex.restrictScalars X.hom).map (colimitAugmentation hI α) =
      sectionsAugmentation α X.pair ≫ LocalCohomology.singleRingHom X.hom := by
  rw [germComplexMap_eq, Category.assoc, colimitComplexMap_augmentation,
    colimitAugmentation_self, Category.assoc, Iso.inv_hom_id_assoc]

/-! ### The one remaining base-change statement -/

/-- **The base-change statement at the germ maps.** For every pair `(A, I)` with `I` finitely
generated and every object `X` of the index category of step 2 of [Stacks, Tag 099D], the
comparison `𝒦•(X.pair) ⊗^L_{X.pair.ring} A ⟶ K(A, I)` built from the germ map is an isomorphism
in `D(A)`.

By `Stacks.PairSite.germComplexMap_eq` this is condition (c) of the tag for the ring maps out of
the presented pairs; it is what the filtered colimit of step 2 is supposed to produce, and it is
the one statement that conditions (c) and (d) for an arbitrary pair need. It holds at
`X = Stacks.PairSite.PairOver.self P` for a presented pair `P`, by
`Stacks.PairSite.isIso_derivedBaseChange_colimitComplexMap_self`, and in general by
`Stacks.PairSite.germBaseChange`: the filtered-colimit argument, resting on the identification
`colim_{Y over X} (Y.pair.ring ⊗_{X.pair.ring} P) ≅ A ⊗_{X.pair.ring} P` for a K-flat
replacement `P` of `𝒦•(X.pair)`. -/
def GermBaseChange (Dat : PresentedCechDatum.{u}) : Prop :=
  ∀ {A : Type u} [CommRing A] {I : Ideal A} (hI : I.FG) (X : PairOver A I),
    IsIso (LocalCohomology.derivedBaseChange X.hom (germComplexMap hI Dat.complex X))

/-- **The base-change statement at the germ maps holds when the pair is a presented pair.** An
object `X` of the index category of `(P.ring, P.ideal)` *is* a morphism of pairs `X.pair ⟶ P`
(`Stacks.PairSite.PairOver.toSelf`), so this is
`Stacks.PairSite.isIso_derivedBaseChange_colimitComplexMap_self`, transported along
`Stacks.PairSite.germComplexMap_eq`. In other words
`Stacks.PairSite.GermBaseChange` is known at the presented pairs; what is missing is an
arbitrary pair `(A, I)`. -/
theorem isIso_derivedBaseChange_germComplexMap_presented (Dat : PresentedCechDatum.{u})
    (P : Pair.{u}) (X : PairOver P.ring P.ideal) :
    IsIso (LocalCohomology.derivedBaseChange X.hom
      (germComplexMap P.ideal_fg Dat.complex X)) := by
  have hbc : IsIso (LocalCohomology.derivedBaseChange X.hom
      (colimitComplexMap X.hom X.pair.ideal_fg P.ideal_fg X.map_ideal.symm Dat.complex)) :=
    isIso_derivedBaseChange_colimitComplexMap_self Dat (Hom.toHom (toSelf X))
  have hmap : IsIso ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u,
        u, u} X.hom).functor.map
      (DerivedCategory.Q.map (colimitComplexSelfIso X.pair Dat.complex).inv)) := inferInstance
  have heq : LocalCohomology.derivedBaseChange X.hom
        (germComplexMap P.ideal_fg Dat.complex X) =
      (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
          X.hom).functor.map
        (DerivedCategory.Q.map (colimitComplexSelfIso X.pair Dat.complex).inv) ≫
        LocalCohomology.derivedBaseChange X.hom
          (colimitComplexMap X.hom X.pair.ideal_fg P.ideal_fg X.map_ideal.symm Dat.complex) :=
    (congrArg (fun w => LocalCohomology.derivedBaseChange X.hom w)
        (germComplexMap_eq P.ideal_fg Dat.complex X)).trans
      (LocalCohomology.derivedBaseChange_comp_left X.hom _ _)
  rw [heq]
  exact LocalCohomology.isIso_comp_aux _ _ hmap hbc

/-- **The germ map at the transport of an object is the germ map followed by datum (3).** This is
`Stacks.PairSite.PairOver.colimitMap_germAt` read on complexes: the germ at
`(transport φ).obj X` of a complex of pair-modules factors through the germ at `X` and the
comparison map of datum (3) along `φ`. -/
theorem germComplexMap_transport (φ : A →+* B) (hI : I.FG) (hJ : J.FG)
    (hφ : J = Ideal.map φ I) (K : CochainComplex PairModule.{u} ℤ) (X : PairOver A I) :
    germComplexMap hJ K ((transport φ hφ).obj X) =
      germComplexMap hI K X ≫
        (CochainComplex.restrictScalars X.hom).map (colimitComplexMap φ hI hJ hφ K) ≫
          (LocalCohomology.restrictScalarsCompComplexIso X.hom φ).hom.app
            ((colimitComplexFunctor hJ).obj K) :=
  HomologicalComplex.hom_ext _ _ fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun m =>
      (colimitMap_germAt φ hI hJ hφ (K.X n) X m).symm)

/-- **Condition (c) of [Stacks, Tag 099D] for the colimit complex, at every ring map**, granted
the base-change statement at the germ maps.

Choose an object `X` of the index category of `(A, I)`. Its transport along `φ` is an object of
the index category of `(B, J)` with the same pair and with structure map `φ ∘ X.hom`, and the
germ map there factors as the germ map at `X` followed by the comparison map of datum (3)
(`Stacks.PairSite.germComplexMap_transport`). The transitivity of the base-change comparison
(`Stacks.LocalCohomology.derivedBaseChange_comp`) then exhibits the comparison at `φ ∘ X.hom` as
the composite of an isomorphism, the image of the comparison at `X.hom`, and the comparison at
`φ`; the first two are isomorphisms, and the first and the whole are, so the comparison at `φ`
is. -/
theorem colimitBaseChange_of_germBaseChange (Dat : PresentedCechDatum.{u})
    (h : GermBaseChange Dat) : ColimitBaseChange Dat := by
  intro A B _ _ φ I hI J hJ hφ
  obtain ⟨X⟩ := PairOver.nonempty (I := I) hI
  have : IsIso (LocalCohomology.derivedBaseChange X.hom
    (germComplexMap hI Dat.complex X)) := h hI X
  have hc := h hJ ((transport φ hφ).obj X)
  rw [germComplexMap_transport φ hI hJ hφ] at hc
  have hc2 := LocalCohomology.derivedBaseChange_comp X.hom φ (germComplexMap hI Dat.complex X)
    (colimitComplexMap φ hI hJ hφ Dat.complex) ▸ hc
  have hHi : IsIso
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp X.hom φ).inv.app
        (DerivedCategory.Q.obj (sectionsComplex Dat.complex X.pair))) := inferInstance
  have hmap : IsIso
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
        φ).functor.map (LocalCohomology.derivedBaseChange X.hom
          (germComplexMap hI Dat.complex X))) := inferInstance
  exact LocalCohomology.isIso_of_isIso_comp₂ _ _ _ hHi hmap hc2

end Stacks.PairSite

end
