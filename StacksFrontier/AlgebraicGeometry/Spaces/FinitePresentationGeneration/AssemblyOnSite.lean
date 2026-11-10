module

public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.GeometryBiprod

/-!
# Closure properties of finite presentation on a site, for the assembly of Stacks 07V9

Three facts about Mathlib's `SheafOfModules.IsFinitePresentation` on an arbitrary site, used by
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Assembly`:

* a zero sheaf of modules is of finite presentation: on every object it is the cokernel of the
  identity of the free module on the empty type;
* finite presentation is closed under finite coproducts: the binary case is
  `Stacks.SheafOfModules.isFinitePresentation_biprod`, the empty case is the zero module, and
  `CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts.mk'` assembles them;
* finite presentation in the sense of Mathlib implies the on-site rendering
  `SheafOfModules.IsFinitePresentationOnSite`: the finite presentations on the members of a
  covering family restrict to every object mapping to one of them
  (`Stacks.SheafOfModules.LocalKernel.presentationOver`), and a finite presentation is a finite
  global presentation (`SheafOfModules.HasFiniteGlobalPresentation.of_presentation'`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v₁ u₁

namespace AlgebraicGeometry.Space.FpAssembly

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective

/-- Supplied explicitly: instance search for colimits of presheaves of modules times out under
Lean v4.35.0. -/
local instance : HasColimitsOfSize.{u, u} (PresheafOfModules.{u} R.obj) :=
  @PresheafOfModules.hasColimitsOfSize _ _ R.obj
    (inferInstance : HasColimitsOfSize.{u, u} AddCommGrpCat.{u})

local instance : HasColimitsOfSize.{u, u} (SheafOfModules.{u} R) := inferInstance

local instance : HasFiniteCoproducts (SheafOfModules.{u} R) :=
  @hasFiniteCoproducts_of_hasCoproducts.{u} _ _ fun _ => HasColimitsOfSize.has_colimits_of_shape _

local instance : HasBinaryCoproducts (SheafOfModules.{u} R) :=
  HasColimitsOfSize.has_colimits_of_shape (self := hasColimitsOfSizeShrink.{0, 0} _) _

/-- A zero sheaf of modules has a finite presentation: it is the cokernel of the identity of the
free module on the empty type. -/
def presentationOfIsZero {M : SheafOfModules.{u} R} (hM : IsZero M) : M.Presentation :=
  SheafOfModules.presentationOfIsCokernelFree (𝟙 (SheafOfModules.free (R := R) PEmpty.{u + 1}))
    (0 : SheafOfModules.free PEmpty.{u + 1} ⟶ M) (by simp)
    (CokernelCofork.IsColimit.ofEpiOfIsZero _ inferInstance hM)

/-- The presentation of a zero module is finite. -/
instance presentationOfIsZero_isFinite {M : SheafOfModules.{u} R} (hM : IsZero M) :
    (presentationOfIsZero hM).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A zero sheaf of modules is of finite presentation.** -/
theorem isFinitePresentation_of_isZero {M : SheafOfModules.{u} R} (hM : IsZero M) :
    M.IsFinitePresentation := by
  let q : M.QuasicoherentData :=
    { I := C
      X := id
      coversTop := fun U => GrothendieckTopology.covering_of_eq_top J (by
        ext V f
        simp only [Sieve.top_apply, iff_true]
        exact (Sieve.mem_ofObjects_iff _ _).2 ⟨V, ⟨𝟙 V⟩⟩)
      presentation := fun U => presentationOfIsZero
        ((SheafOfModules.overFunctor R U).map_isZero hM) }
  exact ⟨⟨q, ⟨fun U => presentationOfIsZero_isFinite _⟩⟩⟩

/-- Finite presentation contains a zero object. -/
instance containsZero_isFinitePresentation :
    (SheafOfModules.isFinitePresentation R).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := SheafOfModules.{u} R)
    exact ⟨Z, hZ, isFinitePresentation_of_isZero hZ⟩

/-- Finite presentation is closed under binary coproducts. -/
instance isClosedUnderBinaryCoproducts_isFinitePresentation :
    (SheafOfModules.isFinitePresentation R).IsClosedUnderBinaryCoproducts where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    have h1 : (p.diag.obj ⟨.left⟩).IsFinitePresentation := p.prop_diag_obj ⟨.left⟩
    have h2 : (p.diag.obj ⟨.right⟩).IsFinitePresentation := p.prop_diag_obj ⟨.right⟩
    let e : X ≅ p.diag.obj ⟨.left⟩ ⊞ p.diag.obj ⟨.right⟩ :=
      p.isColimit.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
        HasColimit.isoOfNatIso (diagramIsoPair p.diag) ≪≫ (biprod.isoCoprod _ _).symm
    exact (SheafOfModules.isFinitePresentation R).prop_of_iso e.symm
      (Stacks.SheafOfModules.isFinitePresentation_biprod _ _ h1 h2)

/-- **A finite coproduct of sheaves of modules of finite presentation is of finite
presentation.** -/
theorem isFinitePresentation_sigma {ι : Type*} [Finite ι] (G : ι → SheafOfModules.{u} R)
    [HasCoproduct G] (hG : ∀ i, (G i).IsFinitePresentation) :
    (∐ G).IsFinitePresentation :=
  have : (SheafOfModules.isFinitePresentation R).IsClosedUnderFiniteCoproducts :=
    ObjectProperty.IsClosedUnderFiniteCoproducts.mk'
  (SheafOfModules.isFinitePresentation R).prop_coproduct hG

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Finite presentation in the sense of Mathlib implies finite presentation on the site.**
The finite presentations of `M` on the members of a covering family restrict to every object
mapping to one of them, and the objects of the site mapping both to a given object `U` and to
some member of the family cover `U`. -/
theorem isFinitePresentationOnSite_of_isFinitePresentation (M : SheafOfModules.{u} R)
    [M.IsFinitePresentation] : M.IsFinitePresentationOnSite := by
  let : ∀ (V W : C) (f : W ⟶ V), PreservesColimitsOfSize.{u, u}
      (SheafOfModules.overMap.{u} R f) :=
    fun _ _ f => Stacks.SheafOfModules.overMap_preservesColimits R f
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  refine ⟨fun U => ⟨Σ (W : C) (i : q.I), (W ⟶ U) × (W ⟶ q.X i), fun a => a.1,
    fun a => a.2.2.1, ?_, fun a => ?_⟩⟩
  · refine J.superset_covering ?_ (q.coversTop U)
    intro W g hg
    obtain ⟨i, ⟨h⟩⟩ := (Sieve.mem_ofObjects_iff _ _).1 hg
    exact (Sieve.mem_ofArrows_iff _ _ g).mpr ⟨⟨W, i, g, h⟩, 𝟙 W, (Category.id_comp g).symm⟩
  · have := hq.isFinite_presentation a.2.1
    exact SheafOfModules.HasFiniteGlobalPresentation.of_presentation'
      (Stacks.SheafOfModules.LocalKernel.presentationOver a.2.2.2 (q.presentation a.2.1))
      inferInstance

section Vanishing

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A section of a sheaf of modules whose restrictions to the members of a covering sieve vanish
is zero: a sheaf is separated. -/
theorem eq_zero_of_forall_mem_sieve (Q : SheafOfModules.{u} R) {V : C}
    (y : Q.val.obj (Opposite.op V)) {T : Sieve V} (hT : T ∈ J V)
    (h : ∀ ⦃W : C⦄ (f : W ⟶ V), T f → Q.val.map f.op y = 0) : y = 0 :=
  Q.isSheaf.isSeparated _ _ hT y 0 (fun W f hf => by
    change Q.val.map f.op y = Q.val.map f.op 0
    rw [h f hf, map_zero])

/-- A morphism of sheaves of modules vanishes as soon as, for every section `x` of its source,
its values on the restrictions of `x` to the members of some covering sieve vanish. -/
theorem hom_eq_zero_of_forall_sieve {M Q : SheafOfModules.{u} R} (g : M ⟶ Q)
    (h : ∀ (V : C) (x : M.val.obj (Opposite.op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃W : C⦄ (f : W ⟶ V), T f → g.val.app (Opposite.op W) (M.val.map f.op x) = 0) :
    g = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  ext x
  obtain ⟨T, hT, hx⟩ := h V.unop x
  exact (eq_zero_of_forall_mem_sieve Q _ hT fun W f hf =>
    (PresheafOfModules.naturality_apply g.val f.op x).symm.trans (hx f hf)).trans rfl

/-- A morphism of sheaves of modules vanishes as soon as it vanishes on every object with a
morphism to a member of a family covering the final object. -/
theorem hom_eq_zero_of_coversTop {M Q : SheafOfModules.{u} R} (g : M ⟶ Q) {ι : Type*}
    {Y : ι → C} (hY : J.CoversTop Y)
    (h : ∀ (i : ι) ⦃W : C⦄ (_ : W ⟶ Y i), g.val.app (Opposite.op W) = 0) : g = 0 := by
  refine hom_eq_zero_of_forall_sieve g fun V x => ⟨Sieve.ofObjects Y V, hY V, ?_⟩
  intro W f hf
  obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff _ _).1 hf
  rw [h i a]
  rfl

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A morphism out of a sheaf of modules vanishes as soon as it kills a family of generating
sections. -/
theorem eq_zero_of_generatingSections {N Q : SheafOfModules.{u} R} (σ : N.GeneratingSections)
    (h : N ⟶ Q) (hs : ∀ i, SheafOfModules.sectionsMap h (σ.s i) =
      SheafOfModules.sectionsMap (0 : N ⟶ Q) (σ.s i)) : h = 0 := by
  rw [← cancel_epi σ.π, comp_zero, ← comp_zero (f := σ.π) (Z := Q),
    SheafOfModules.GeneratingSections.π, SheafOfModules.freeHomEquiv_symm_comp,
    SheafOfModules.freeHomEquiv_symm_comp]
  exact congrArg _ (funext hs)

end Vanishing

end AlgebraicGeometry.Space.FpAssembly

end
