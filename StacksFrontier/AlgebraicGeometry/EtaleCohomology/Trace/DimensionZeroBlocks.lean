module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTwistStalk
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.TraceAdditivity

/-!
# The block decomposition of the canonical Frobenius twist in dimension zero

Let `k` be a finite field, `Y` a scheme finite étale over `k` and `k̄` an algebraically closed
extension of `k`.  The global sections of a sheaf `G` on `Y_k̄` are the product of its values on
the `k̄`-points `ȳ` of `Y_k̄`, and the canonical Frobenius twist `G ⟶ π̄_* G` permutes these
blocks: the block of the twisted endomorphism from `ȳ` to `ȳ'` vanishes unless `ȳ' ≫ π̄ = ȳ`.  In
particular the diagonal block at `ȳ` vanishes unless `ȳ` is fixed by `π̄`, and at a fixed point it
is the twist at `ȳ` followed by restriction along `ȳ ⟶ π̄^* ȳ`.  This is the computation behind
Step 2 of the proof of [Stacks, Tag 03UG].

## Main definitions

* `Stacks.EtaleCohomology.baseChangeTop`: the base change to `Y_k̄` of the final object of the
  small étale site of `Spec k̄`, a final object of the small étale site of `Y_k̄`.
* `Stacks.EtaleCohomology.sectionsTwistEndo`: the endomorphism of the sections over
  `baseChangeTop` induced by the canonical Frobenius twist.
* `Stacks.EtaleCohomology.blockRestriction`, `Stacks.EtaleCohomology.blockInclusion`: the
  projections to, and inclusions of, the values on the `k̄`-points.

## Main results

* `Stacks.EtaleCohomology.sum_blockRestriction_comp_blockInclusion`: the blocks decompose the
  identity.
* `Stacks.EtaleCohomology.sectionsTwistEndo_comp_blockRestriction`: the twisted endomorphism
  followed by restriction to `ȳ` is restriction to `ȳ ≫ π̄` followed by the twist there.
* `Stacks.EtaleCohomology.blockInclusion_comp_sectionsTwistEndo_comp_blockRestriction_of_ne`:
  the diagonal block at a point not fixed by `π̄` vanishes.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r v

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize HasDerivedCategory.standard

/-! ### The trace through a decomposition of a functor -/

section Generic

open CategoryTheory.FilteredDerived

variable {R : Type r} [Ring R] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]

/-- **The trace through a decomposition of a functor into blocks.**  If natural projections
`p_i : Φ ⟶ B_i` and inclusions `inc_i : B_i ⟶ Φ` of additive functors to `R`-modules decompose
the identity of `Φ`, then for every complex `K` with `Φ(K)` and all `B_i(K)` perfect, the trace of
the termwise endomorphism `e(K)` of `Φ(K)` attached to `e : Φ ⟶ Φ` is the sum of the traces of the
termwise diagonal blocks `inc_i ≫ e ≫ p_i`. -/
theorem perfectDerivedTrace_mapHomologicalComplex_eq_sum
    (Φ : 𝒞 ⥤ ModuleCat.{v} R) [Φ.Additive] {ι : Type*} (s : Finset ι)
    (B : ι → 𝒞 ⥤ ModuleCat.{v} R) [∀ i, (B i).Additive] (pr : ∀ i, Φ ⟶ B i)
    (inc : ∀ i, B i ⟶ Φ) (h : ∑ i ∈ s, pr i ≫ inc i = 𝟙 Φ) (e : Φ ⟶ Φ)
    (K : CochainComplex 𝒞 ℤ)
    (hK : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
    (hB : ∀ i, StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (((B i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) :
    perfectDerivedTrace R ⟨_, hK⟩
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e _).app K)) =
      ∑ i ∈ s, perfectDerivedTrace R ⟨_, hB i⟩
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (inc i ≫ e ≫ pr i) _).app K)) := by
  refine (perfectDerivedTrace_eq_sum_of_sum_comp_eq_id R ⟨_, hK⟩ s (fun i => ⟨_, hB i⟩)
    (fun i => DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (pr i) _).app K))
    (fun i => DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (inc i) _).app K)) ?_ _).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  · have hc : ∑ i ∈ s, (NatTrans.mapHomologicalComplex (pr i) (ComplexShape.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex (inc i) (ComplexShape.up ℤ)).app K = 𝟙 _ := by
      ext n : 1
      refine ((HomologicalComplex.eval _ (ComplexShape.up ℤ) n).map_sum _ s).trans ?_
      simpa using congrArg (fun φ => φ.app (K.X n)) h
    simp_rw [← Functor.map_comp, ← Functor.map_sum, hc, CategoryTheory.Functor.map_id]
  · simp only [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app, Functor.map_comp]

end Generic

section Blocks

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]

/-- The base change to `Y_k̄` of the final object of the small étale site of `Spec k̄`. -/
abbrev baseChangeTop : (fieldBaseChange Y kbar).Etale :=
  (smallEtaleBaseChange (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
    (Scheme.Etale.mk (𝟙 (Spec (.of kbar))))

private lemma comp_fst_chase {C : Type*} [Category C] {V P T S : C} (m : V ⟶ P) (fst : P ⟶ T)
    (snd : P ⟶ S) (g : S ⟶ T) (v : V ⟶ S) (h1 : m ≫ snd = v) (h2 : fst ≫ 𝟙 T = snd ≫ g) :
    m ≫ fst = v ≫ g := by
  rw [← h1, Category.assoc, ← h2, Category.comp_id]

/-- The morphism of an étale `Y_k̄`-scheme to the base change of the final object. -/
abbrev toBaseChangeTop (V : (fieldBaseChange Y kbar).Etale) : V ⟶ baseChangeTop Y kbar :=
  MorphismProperty.Over.homMk
    (pullback.lift (V.hom ≫ pullback.snd Y.hom (specAlgebraMap k kbar)) V.hom
      (Category.comp_id _)) (pullback.lift_snd _ _ _)

omit [Fintype k] [IsAlgClosed kbar] in
/-- Every morphism to the base change of the final object is the canonical one. -/
lemma eq_toBaseChangeTop {V : (fieldBaseChange Y kbar).Etale} (m : V ⟶ baseChangeTop Y kbar) :
    m = toBaseChangeTop Y kbar V :=
  smallEtaleBaseChange_hom_ext _
    ((comp_fst_chase _ _ _ _ _ (smallEtaleBaseChange_w _ m) pullback.condition).trans
      (pullback.lift_fst _ _ _).symm)

/-- The base change of the final object is a final object of the small étale site of `Y_k̄`. -/
def isTerminalBaseChangeTop : IsTerminal (baseChangeTop Y kbar) :=
  IsTerminal.ofUniqueHom (toBaseChangeTop Y kbar) (fun _ m => eq_toBaseChangeTop Y kbar m)

variable [Etale Y.hom]

/-- Evaluation of `C|_{Y_k̄}` at an étale `Y_k̄`-scheme, as a functor of the sheaf `C` on `Y`. -/
abbrev restrictionSections (V : (fieldBaseChange Y kbar).Etale) :
    EtaleModules.{u, r} Λ Y.left ⥤ ModuleCat.{max (u + 1) r} Λ :=
  etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar) ⋙
    sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
      (CategoryTheory.evaluation (fieldBaseChange Y kbar).Etaleᵒᵖ
        (ModuleCat.{max (u + 1) r} Λ)).obj (op V)

/-- Restriction along a morphism of étale `Y_k̄`-schemes, natural in the sheaf on `Y`. -/
abbrev restrictionSectionsMap {V V' : (fieldBaseChange Y kbar).Etale} (g : V ⟶ V') :
    restrictionSections Λ Y kbar V' ⟶ restrictionSections Λ Y kbar V :=
  Functor.whiskerLeft _ (Functor.whiskerLeft _
    ((CategoryTheory.evaluation (fieldBaseChange Y kbar).Etaleᵒᵖ
      (ModuleCat.{max (u + 1) r} Λ)).map g.op))

/-- The terminal morphism of `baseChangeTop` to the final object `Y_k̄` of the small étale site. -/
abbrev baseChangeTopToTop : baseChangeTop Y kbar ⟶ Scheme.Etale.mk (𝟙 (fieldBaseChange Y kbar)) :=
  (isTerminalEtaleMkId (fieldBaseChange Y kbar)).from _

open scoped Classical in
/-- The `k̄`-points of `Y_k̄` over `k̄` form a finite set. -/
instance [IsFinite Y.hom] : Fintype (EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar))) :=
  Fintype.ofFinite _

/-- **Restriction to a block**: from the sections over `baseChangeTop` to the sections over the
`k̄`-point `ȳ`. -/
abbrev blockRestriction (y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar))) :
    restrictionSections Λ Y kbar (baseChangeTop Y kbar) ⟶
      restrictionSections Λ Y kbar (etaleSectionObj _ y) :=
  restrictionSectionsMap Λ Y kbar (toBaseChangeTop Y kbar _)

/-- **Inclusion of a block**: extension by zero from the sections over the `k̄`-point `ȳ` to the
sections over `baseChangeTop`. -/
def blockInclusion (y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar))) :
    restrictionSections Λ Y kbar (etaleSectionObj _ y) ⟶
      restrictionSections Λ Y kbar (baseChangeTop Y kbar) where
  app L := etaleSectionsInclusion Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L) y ≫
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj.map
      (baseChangeTopToTop Y kbar).op
  naturality L L' φ := by
    have h₁ := etaleSectionsInclusion_naturality Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map φ) y
    have h₂ :=
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map φ).hom.naturality
        (baseChangeTopToTop Y kbar).op
    change
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map φ).hom.app _ ≫ _ ≫ _ =
        (_ ≫ _) ≫ ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map φ).hom.app _
    rw [Category.assoc, h₂, reassoc_of% h₁]

omit [Fintype k] in
/-- The component of `blockInclusion` at a sheaf `L`. -/
lemma blockInclusion_app (y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (L : EtaleModules.{u, r} Λ Y.left) :
    (blockInclusion Λ Y kbar y).app L =
      etaleSectionsInclusion Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L) y ≫
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj.map
        (baseChangeTopToTop Y kbar).op :=
  rfl

omit [Fintype k] in
/-- The block inclusion at `ȳ` followed by the block restriction at `ȳ'` is the identity if
`ȳ = ȳ'` and zero otherwise; here the case `ȳ = ȳ'`. -/
@[reassoc (attr := simp)]
lemma blockInclusion_comp_blockRestriction_self
    (y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar))) :
    blockInclusion Λ Y kbar y ≫ blockRestriction Λ Y kbar y = 𝟙 _ := by
  ext L : 2
  have h : toBaseChangeTop Y kbar (etaleSectionObj _ y) ≫ baseChangeTopToTop Y kbar =
      etaleSectionToTop _ y := (isTerminalEtaleMkId _).hom_ext _ _
  change (etaleSectionsInclusion Λ _ _ y ≫
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj.map
        (baseChangeTopToTop Y kbar).op) ≫
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj.map
        (toBaseChangeTop Y kbar (etaleSectionObj _ y)).op = 𝟙 _
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, h]
  exact etaleSectionsInclusion_restrict_self Λ _ _ y

omit [Fintype k] in
/-- The block inclusion at `ȳ` followed by the block restriction at a different `ȳ'` vanishes. -/
@[reassoc]
lemma blockInclusion_comp_blockRestriction_of_ne
    {y y' : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar))} (hy : y ≠ y') :
    blockInclusion Λ Y kbar y ≫ blockRestriction Λ Y kbar y' = 0 := by
  ext L : 2
  have h : toBaseChangeTop Y kbar (etaleSectionObj _ y') ≫ baseChangeTopToTop Y kbar =
      etaleSectionToTop _ y' := (isTerminalEtaleMkId _).hom_ext _ _
  change (etaleSectionsInclusion Λ _ _ y ≫
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj.map
        (baseChangeTopToTop Y kbar).op) ≫
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj.map
        (toBaseChangeTop Y kbar (etaleSectionObj _ y')).op = 0
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, h]
  exact etaleSectionsInclusion_restrict_of_ne Λ _ _ hy

omit [Fintype k] in
/-- **The blocks decompose the identity.** -/
lemma sum_blockRestriction_comp_blockInclusion [Finite k] [IsFinite Y.hom] :
    ∑ y, blockRestriction Λ Y kbar y ≫ blockInclusion Λ Y kbar y = 𝟙 _ := by
  have := Fintype.ofFinite k
  ext L : 2
  set G := ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj
  have h₁ : ∀ y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar)),
      toBaseChangeTop Y kbar (etaleSectionObj _ y) =
        etaleSectionToTop _ y ≫ toBaseChangeTop Y kbar _ := fun y =>
    (eq_toBaseChangeTop Y kbar _).symm
  have h₂ : baseChangeTopToTop Y kbar ≫ toBaseChangeTop Y kbar _ = 𝟙 _ :=
    (eq_toBaseChangeTop Y kbar _).trans (eq_toBaseChangeTop Y kbar _).symm
  have hsum := sum_etaleSections_restrict_inclusion Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L)
  rw [NatTrans.app_sum]
  change ∑ y, G.map (toBaseChangeTop Y kbar (etaleSectionObj _ y)).op ≫
    (etaleSectionsInclusion Λ _ _ y ≫ G.map (baseChangeTopToTop Y kbar).op) = 𝟙 _
  simp_rw [h₁, op_comp, Functor.map_comp, Category.assoc, ← Preadditive.comp_sum,
    ← Category.assoc, ← Preadditive.sum_comp]
  change G.map (toBaseChangeTop Y kbar _).op ≫ (∑ y, G.map (etaleSectionToTop _ y).op ≫
    etaleSectionsInclusion Λ _ _ y) ≫ G.map (baseChangeTopToTop Y kbar).op = 𝟙 _
  rw [hsum, Category.id_comp, ← Functor.map_comp, ← op_comp, h₂, op_id,
    CategoryTheory.Functor.map_id]

end Blocks

section Twist

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Etale Y.hom]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The comparison `T ⟶ π̄^* T` for the base change `T` of the final object, from
`pr₂ = π̄ ≫ pr₂`. -/
abbrev baseChangeTopFrobenius :
    baseChangeTop Y kbar ⟶
      (smallEtaleBaseChange (geometricFrobeniusBaseChange Y kbar p q hcard)).obj
        (baseChangeTop Y kbar) :=
  (smallEtaleBaseChangeComp' (geometricFrobeniusBaseChange Y kbar p q hcard)
    (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
    (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm).hom.app
      (Scheme.Etale.mk (𝟙 (Spec (.of kbar))))

/-- The base change along `π̄` of `baseChangeTop` is again a final object. -/
def isTerminalFrobeniusBaseChangeTop :
    IsTerminal ((smallEtaleBaseChange (geometricFrobeniusBaseChange Y kbar p q hcard)).obj
      (baseChangeTop Y kbar)) :=
  (isTerminalBaseChangeTop Y kbar).ofIso
    ((smallEtaleBaseChangeComp' (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm).app
        (Scheme.Etale.mk (𝟙 (Spec (.of kbar)))))

/-- **The canonical Frobenius twist on the sections over `baseChangeTop`**: the twist
`C|_{Y_k̄} ⟶ π̄_*(C|_{Y_k̄})` at `T`, followed by restriction along `T ⟶ π̄^* T`. -/
def sectionsTwistEndo :
    restrictionSections Λ Y kbar (baseChangeTop Y kbar) ⟶
      restrictionSections Λ Y kbar (baseChangeTop Y kbar) :=
  Functor.whiskerRight (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard)
      (sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
        (CategoryTheory.evaluation (fieldBaseChange Y kbar).Etaleᵒᵖ
          (ModuleCat.{max (u + 1) r} Λ)).obj (op (baseChangeTop Y kbar))) ≫
    restrictionSectionsMap Λ Y kbar (baseChangeTopFrobenius Y kbar p q hcard)

/-- The `k̄`-point `ȳ ≫ π̄` of `Y_k̄`. -/
abbrev frobeniusSection (y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar))) :
    EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar)) :=
  ⟨y.1 ≫ geometricFrobeniusBaseChange Y kbar p q hcard, by
    rw [Category.assoc, geometricFrobeniusBaseChange_comp_snd, y.2]⟩

/-- The morphism `ȳ ⟶ π̄^* ȳ₂` of étale `Y_k̄`-schemes attached to `ȳ₂ = ȳ ≫ π̄`. -/
def sectionFrobeniusLift {y y₂ : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar))}
    (h : y₂.1 = y.1 ≫ geometricFrobeniusBaseChange Y kbar p q hcard) :
    etaleSectionObj _ y ⟶
      (smallEtaleBaseChange (geometricFrobeniusBaseChange Y kbar p q hcard)).obj
        (etaleSectionObj _ y₂) :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 _) y.1 ((Category.id_comp _).trans h)) (pullback.lift_snd _ _ _)

/-- The twist at the `k̄`-point `ȳ₂` followed by restriction along `ȳ ⟶ π̄^* ȳ₂`. -/
def pointTwist {y y₂ : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar))}
    (h : y₂.1 = y.1 ≫ geometricFrobeniusBaseChange Y kbar p q hcard) :
    restrictionSections Λ Y kbar (etaleSectionObj _ y₂) ⟶
      restrictionSections Λ Y kbar (etaleSectionObj _ y) :=
  Functor.whiskerRight (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard)
      (sheafToPresheaf _ (ModuleCat.{max (u + 1) r} Λ) ⋙
        (CategoryTheory.evaluation (fieldBaseChange Y kbar).Etaleᵒᵖ
          (ModuleCat.{max (u + 1) r} Λ)).obj (op (etaleSectionObj _ y₂))) ≫
    restrictionSectionsMap Λ Y kbar (sectionFrobeniusLift Y kbar p q hcard h)

private lemma twistBlockChase {D : Type*} [Category D] {A B C E F : D} (τT : A ⟶ B) (Gc : B ⟶ A)
    (Gt : A ⟶ C) (Gm : B ⟶ E) (Gl : E ⟶ C) (Gt₂ : A ⟶ F) (τY : F ⟶ E) (hct : Gc ≫ Gt = Gm ≫ Gl)
    (hτ : Gt₂ ≫ τY = τT ≫ Gm) :
    (τT ≫ Gc) ≫ Gt = Gt₂ ≫ τY ≫ Gl := by
  rw [Category.assoc, hct, reassoc_of% hτ]

omit [IsAlgClosed kbar] in
/-- **The twisted endomorphism permutes the blocks**: followed by restriction to `ȳ`, it is
restriction to `ȳ₂ = ȳ ≫ π̄` followed by the twist at `ȳ₂`. -/
lemma sectionsTwistEndo_comp_blockRestriction
    {y y₂ : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar))}
    (h : y₂.1 = y.1 ≫ geometricFrobeniusBaseChange Y kbar p q hcard) :
    sectionsTwistEndo Λ Y kbar p q hcard ≫ blockRestriction Λ Y kbar y =
      blockRestriction Λ Y kbar y₂ ≫ pointTwist Λ Y kbar p q hcard h := by
  ext L : 2
  set G := ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj L).obj
  set τ := ((frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app L).hom
  have hτ := τ.naturality (toBaseChangeTop Y kbar (etaleSectionObj _ y₂)).op
  have ht : toBaseChangeTop Y kbar (etaleSectionObj _ y) ≫ baseChangeTopFrobenius Y kbar p q hcard =
      sectionFrobeniusLift Y kbar p q hcard h ≫
        (smallEtaleBaseChange (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          (toBaseChangeTop Y kbar (etaleSectionObj _ y₂)) :=
    (isTerminalFrobeniusBaseChangeTop Y kbar p q hcard).hom_ext _ _
  change (τ.app _ ≫ G.map (baseChangeTopFrobenius Y kbar p q hcard).op) ≫
      G.map (toBaseChangeTop Y kbar (etaleSectionObj _ y)).op =
    G.map (toBaseChangeTop Y kbar (etaleSectionObj _ y₂)).op ≫ τ.app _ ≫
      G.map (sectionFrobeniusLift Y kbar p q hcard h).op
  have hct : G.map (baseChangeTopFrobenius Y kbar p q hcard).op ≫
      G.map (toBaseChangeTop Y kbar (etaleSectionObj _ y)).op =
        G.map ((smallEtaleBaseChange (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          (toBaseChangeTop Y kbar (etaleSectionObj _ y₂))).op ≫
        G.map (sectionFrobeniusLift Y kbar p q hcard h).op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ht]
  exact twistBlockChase _ _ _ _ _ _ _ hct hτ

/-- **The diagonal block at a point not fixed by `π̄` vanishes.** -/
lemma blockInclusion_comp_sectionsTwistEndo_comp_blockRestriction_of_ne
    (y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (hy : y.1 ≫ geometricFrobeniusBaseChange Y kbar p q hcard ≠ y.1) :
    blockInclusion Λ Y kbar y ≫ sectionsTwistEndo Λ Y kbar p q hcard ≫
      blockRestriction Λ Y kbar y = 0 := by
  rw [sectionsTwistEndo_comp_blockRestriction Λ Y kbar p q hcard (y₂ := frobeniusSection Y kbar p q
    hcard y) rfl, blockInclusion_comp_blockRestriction_of_ne_assoc, zero_comp]
  exact fun h => hy (congrArg Subtype.val h).symm

/-- **The diagonal block at a point fixed by `π̄` is the twist there.** -/
lemma blockInclusion_comp_sectionsTwistEndo_comp_blockRestriction_of_eq
    (y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (hy : y.1 = y.1 ≫ geometricFrobeniusBaseChange Y kbar p q hcard) :
    blockInclusion Λ Y kbar y ≫ sectionsTwistEndo Λ Y kbar p q hcard ≫
      blockRestriction Λ Y kbar y = pointTwist Λ Y kbar p q hcard hy := by
  rw [sectionsTwistEndo_comp_blockRestriction Λ Y kbar p q hcard hy,
    blockInclusion_comp_blockRestriction_self_assoc]

end Twist

section Trace

open CategoryTheory.FilteredDerived

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Etale Y.hom] [IsFinite Y.hom]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- Evaluation of `C|_{Y_k̄}` at an étale `Y_k̄`-scheme is an additive functor. -/
instance (V : (fieldBaseChange Y kbar).Etale) : (restrictionSections Λ Y kbar V).Additive :=
  inferInstance

/-- The `k̄`-points of `Y_k̄` fixed by `π̄`. -/
abbrev FixedSections : Type u :=
  {y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar)) //
    y.1 = y.1 ≫ geometricFrobeniusBaseChange Y kbar p q hcard}

open scoped Classical in
/-- **Step 2 of [Stacks, Tag 03UG], block form.**  For `Y` finite étale over `k` and a complex
`C` on `Y`, the trace of the canonical Frobenius twist on the sections of `C|_{Y_k̄}` over the
final object is the sum, over the `k̄`-points `ȳ` fixed by `π̄`, of the traces of the twist at
`ȳ`; the blocks at the other points vanish. -/
theorem perfectDerivedTrace_sectionsTwistEndo_eq_sum
    (C : CochainComplex (EtaleModules.{u, r} Λ Y.left) ℤ)
    (hC : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((restrictionSections Λ Y kbar (baseChangeTop Y kbar)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C)))
    (hP : ∀ y, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((restrictionSections Λ Y kbar (etaleSectionObj _ y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C))) :
    perfectDerivedTrace Λ ⟨_, hC⟩ (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (sectionsTwistEndo Λ Y kbar p q hcard) _).app C)) =
      ∑ y : FixedSections Y kbar p q hcard, perfectDerivedTrace Λ ⟨_, hP y.1⟩
        (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pointTwist Λ Y kbar p q hcard y.2) _).app C)) := by
  rw [perfectDerivedTrace_mapHomologicalComplex_eq_sum
    (restrictionSections Λ Y kbar (baseChangeTop Y kbar)) Finset.univ
    (fun y => restrictionSections Λ Y kbar (etaleSectionObj _ y)) (blockRestriction Λ Y kbar)
    (blockInclusion Λ Y kbar) (sum_blockRestriction_comp_blockInclusion Λ Y kbar) _ C hC hP,
    ← Fintype.sum_subtype_add_sum_subtype
      (fun y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar)) =>
        y.1 = y.1 ≫ geometricFrobeniusBaseChange Y kbar p q hcard)]
  rw [Fintype.sum_eq_zero (fun y : {y // ¬ _} => _) (fun y => ?_), add_zero]
  · refine Fintype.sum_congr _ _ fun y => ?_
    simp only [blockInclusion_comp_sectionsTwistEndo_comp_blockRestriction_of_eq Λ Y kbar p q hcard
      y.1 y.2]
  · rw [blockInclusion_comp_sectionsTwistEndo_comp_blockRestriction_of_ne Λ Y kbar p q hcard y.1
      (fun h => y.2 h.symm)]
    convert perfectDerivedTrace_zero Λ _
    rw [← DerivedCategory.Q.map_zero]
    congr 1

end Trace

end Stacks.EtaleCohomology

end
