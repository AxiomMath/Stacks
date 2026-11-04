module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitColimitMainstreamSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RepresentabilityDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.BoundaryRestrictionVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageRepresentable
public import StacksFrontier.CategoryTheory.Sites.FibreSheaf
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# The torsor of a class in `H^1` with finite constant coefficients

Let `Y` be a scheme, `M` a finite abelian group and `ζ ∈ H^1(Y, M)`. Embed the constant sheaf `M`
into an injective sheaf `I` with quotient `Q`; then `ζ = ∂σ` for a global section `σ` of `Q`,
and the fibre `P` of `I ⟶ Q` over `σ` is a torsor under `M` ([Stacks, Tag 03AJ]). It is a finite
locally constant sheaf of sets, hence represented by a finite étale `Y`-scheme `T`
([Stacks, Tag 03RV]), and `ζ` dies on `T`, the torsor having a section there. This is the first
step of the case `q = 1` of [Stacks, Tag 0EYT].

## Main definitions

* `Stacks.EtaleCohomology.injectiveShortComplex`: the short exact sequence `0 → A → I → Q → 0`
  with `I` injective.
* `Stacks.EtaleCohomology.torsorSheaf`: the fibre of `I ⟶ Q` over a global section of `Q`.
* `Stacks.EtaleCohomology.torsorTranslate`: the translation action of `M` on the torsor.

## Main results

* `Stacks.EtaleCohomology.exists_eq_comp_extClass_of_injective`: a class in `H^1` is the
  boundary of a global section of the quotient by an injective.
* `Stacks.EtaleCohomology.exists_isFinite_iso_uliftYoneda`: the torsor is represented by a
  finite étale `Y`-scheme.
* `Stacks.EtaleCohomology.exists_torsorCover`: a class in `H^1` with finite constant
  coefficients dies on a finite étale `M`-torsor.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

variable {Y : Scheme.{u}}

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **An injective embedding of an abelian sheaf on the small étale site**, as the short complex
`0 → A → I → Q → 0` with `I` injective and `Q` the cokernel. -/
def injectiveShortComplex (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A)) (cokernel.condition _)

/-- The short complex `injectiveShortComplex A` is short exact. -/
theorem injectiveShortComplex_shortExact (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (injectiveShortComplex A).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    (inferInstanceAs (Mono (Injective.ι A))) ⟨fun _ _ h => coequalizer.hom_ext h⟩

/-- The middle term of `injectiveShortComplex A` is injective. -/
instance (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Injective (injectiveShortComplex A).X₂ :=
  inferInstanceAs (Injective (Injective.under A))

/-- The quotient map of `injectiveShortComplex A` is locally surjective. -/
private local instance (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Sheaf.IsLocallySurjective (injectiveShortComplex A).g :=
  have := (injectiveShortComplex_shortExact A).epi_g
  (Sheaf.isLocallySurjective_iff_epi' (φ := (injectiveShortComplex A).g)).2 inferInstance

/-- **A class in degree one is the boundary of a global section of the quotient by an
injective.** -/
theorem exists_eq_comp_extClass_of_injective
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    [Injective S.X₂] (ζ : Sheaf.H.{u + 1} S.X₁ 1) :
    ∃ σ : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ S.X₃,
      (Ext.mk₀ σ).comp hS.extClass (zero_add 1) = ζ := by
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₁ _ hS ζ
    (Ext.eq_zero_of_injective _) (zero_add 1)
  exact ⟨Ext.homEquiv₀ x, by rw [Ext.mk₀_homEquiv₀_apply, hx]⟩

/-- **Short exact sequences of abelian sheaves are left exact on sections.** -/
theorem injective_app_of_shortExact
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (U : Y.Etaleᵒᵖ) : Function.Injective (S.f.hom.app U) := by
  let F := sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj U
  have := hS.mono_f
  exact (AddCommGrpCat.mono_iff_injective (F.map S.f)).1 inferInstance

/-- **Short exact sequences of abelian sheaves are exact in the middle on sections.** -/
theorem exists_app_eq_of_shortExact
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (U : Y.Etaleᵒᵖ) (x : S.X₂.obj.obj U) (hx : S.g.hom.app U x = 0) :
    ∃ y, S.f.hom.app U y = x := by
  let F := sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj U
  have := hS.mono_f
  exact (ShortComplex.ab_exact_iff _).1
    (hS.exact.map_of_mono_of_preservesKernel F inferInstance inferInstance) x hx

/-! ### The torsor -/

section Torsor

variable (M : AddCommGrpCat.{u + 1})
  (σ : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶
    (injectiveShortComplex ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)).X₃)

/-- **The torsor attached to a boundary**: the fibre of the injective embedding of the constant
sheaf `M` over the global section `σ` of the quotient. -/
abbrev torsorSheaf : Sheaf Y.smallEtaleTopology (Type (u + 1)) :=
  FibreSheaf.fibreSheaf
    (injectiveShortComplex ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)).g
    (terminalEtaleIsTerminal Y) (sectionOfHom σ)

/-- **The torsor of a boundary with finite constant coefficients is finite locally constant.** -/
theorem isFiniteLocallyConstant_torsorSheaf [Finite M] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant Y.smallEtaleTopology (torsorSheaf M σ) := by
  have hS := injectiveShortComplex_shortExact
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)
  exact FibreSheaf.isFiniteLocallyConstant.{u + 1} _ _ _ M _ (injective_app_of_shortExact hS)
    (exists_app_eq_of_shortExact hS) (injectiveShortComplex _).zero

/-- The restriction to the size-bounded small étale site of a representable sheaf is the
representable sheaf of the corresponding object, the embedding being fully faithful. -/
def etaleSiteRestrictionUliftYonedaIso (B : BigEtaleSite.{u}) (hY : B.Contains Y)
    (W : SmallEtale B Y hY) :
    haveI := smallEtaleTopology_subcanonical' B ⟨Y, hY⟩
    (SmallEtale.etaleSiteRestriction B Y hY (Type (u + 1))).obj
        ((smallEtaleTopology Y).uliftYoneda.{u + 1}.obj ((SmallEtale.toEtaleSite B Y hY).obj W)) ≅
      (SmallEtale.topology B Y hY).uliftYoneda.{u + 1}.obj W :=
  haveI := smallEtaleTopology_subcanonical' B ⟨Y, hY⟩
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight (NatIso.ofComponents
      (fun U => (Functor.FullyFaithful.ofFullyFaithful
        (SmallEtale.toEtaleSite B Y hY)).homEquiv.symm.toIso)
      (fun f => by
        ext g
        apply (SmallEtale.toEtaleSite B Y hY).map_injective
        simp) : (SmallEtale.toEtaleSite B Y hY).op ⋙
          yoneda.obj ((SmallEtale.toEtaleSite B Y hY).obj W) ≅ yoneda.obj W)
      uliftFunctor.{u + 1})

variable [Finite M] in
/-- **The torsor is represented by a finite étale `Y`-scheme** ([Stacks, Tag 03RV]). -/
theorem exists_isFinite_iso_uliftYoneda :
    ∃ V : Y.Etale, IsFinite V.hom ∧
      Nonempty (torsorSheaf M σ ≅ (smallEtaleTopology Y).uliftYoneda.{u + 1}.obj V) := by
  have : Small.{u} ({Y} : Set Scheme.{u}) := small_single.{u} Y
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small ({Y} : Set Scheme.{u})
  have hY : B.Contains Y := hB Y rfl
  obtain ⟨W, hW, ⟨e⟩⟩ := (isFiniteLocallyConstant_iff_finiteEtaleRepresentable B ⟨Y, hY⟩ _).1
    ((SmallEtale.isFiniteLocallyConstant_iff_toEtaleSite B Y hY (torsorSheaf M σ)).1
      (isFiniteLocallyConstant_torsorSheaf M σ))
  have := smallEtaleTopology_subcanonical' B ⟨Y, hY⟩
  exact ⟨(SmallEtale.toEtaleSite B Y hY).obj W, hW, ⟨(Functor.FullyFaithful.ofFullyFaithful
    (SmallEtale.etaleSiteRestriction B Y hY (Type (u + 1)))).preimageIso
      (e ≪≫ (Sheaf.sheafifiedYonedaIsoUliftYoneda' _).app W ≪≫
        (etaleSiteRestrictionUliftYonedaIso B hY W).symm)⟩⟩

end Torsor

/-! ### Stalks at a geometric point -/

section Point

/-- The forgetful functor from abelian groups preserves filtered colimits of size `u`. -/
instance : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) := by
  have := AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits.{u + 1}
  exact preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)

/-- The unique point of the fibre of the terminal object. -/
def terminalFiberPoint : (Scheme.pointSmallEtale y).fiber.obj (terminalEtale Y) :=
  ((Scheme.pointSmallEtale y).uniqueFiberObj _ (terminalEtaleIsTerminal Y)).default

/-- Every point of a fibre maps to `terminalFiberPoint y` in the fibre of the terminal object. -/
theorem fiber_map_terminal_eq {X : Y.Etale} (x : (Scheme.pointSmallEtale y).fiber.obj X)
    (h : X ⟶ terminalEtale Y) :
    (Scheme.pointSmallEtale y).fiber.map h x = terminalFiberPoint y :=
  ((Scheme.pointSmallEtale y).uniqueFiberObj _ (terminalEtaleIsTerminal Y)).uniq _

/-- **The stalk of a constant presheaf is its value.** -/
theorem bijective_toPresheafFiber_const (M : AddCommGrpCat.{u + 1}) (X : Y.Etale)
    (x : (Scheme.pointSmallEtale y).fiber.obj X) :
    Function.Bijective ((Scheme.pointSmallEtale y).toPresheafFiber X x
      ((Functor.const Y.Etaleᵒᵖ).obj M)) := by
  let Φ := Scheme.pointSmallEtale y
  refine ⟨fun z₁ z₂ h => ?_, fun p => ?_⟩
  · obtain ⟨Z, f, z, -, hf⟩ := (Φ.toPresheafFiber_eq_iff' X x z₁ z₂).1 h
    exact hf
  obtain ⟨X', x', z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective p
  let E : Φ.fiber.Elements := IsCofiltered.min (Φ.fiber.elementsMk X' x')
    (Φ.fiber.elementsMk X x)
  have hl := Φ.toPresheafFiber_w_apply (IsCofiltered.minToLeft
    (Φ.fiber.elementsMk X' x') (Φ.fiber.elementsMk X x)).1 E.2 ((Functor.const _).obj M) z
  have hr := Φ.toPresheafFiber_w_apply (IsCofiltered.minToRight
    (Φ.fiber.elementsMk X' x') (Φ.fiber.elementsMk X x)).1 E.2 ((Functor.const _).obj M) z
  rw [(IsCofiltered.minToLeft (Φ.fiber.elementsMk X' x') (Φ.fiber.elementsMk X x)).2] at hl
  rw [(IsCofiltered.minToRight (Φ.fiber.elementsMk X' x') (Φ.fiber.elementsMk X x)).2] at hr
  exact ⟨z, hr.symm.trans hl⟩

/-- The canonical map from the constant presheaf to the constant sheaf. -/
def toConstantSheaf (M : AddCommGrpCat.{u + 1}) :
    (Functor.const Y.Etaleᵒᵖ).obj M ⟶
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M).obj :=
  toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)

/-- The map from the constant presheaf to the constant sheaf is locally injective. -/
instance (M : AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallyInjective Y.smallEtaleTopology (toConstantSheaf (Y := Y) M) :=
  Presheaf.isLocallyInjective_toSheafify' _ _

/-- The map from the constant presheaf to the constant sheaf is locally surjective. -/
instance (M : AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallySurjective Y.smallEtaleTopology (toConstantSheaf (Y := Y) M) :=
  Presheaf.isLocallySurjective_toSheafify' (J := Y.smallEtaleTopology)
    ((Functor.const Y.Etaleᵒᵖ).obj M)

/-- The constant global section of the constant sheaf attached to an element. -/
def constantSheafGlobalSection (M : AddCommGrpCat.{u + 1}) (m : M) :
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M).obj.obj
      (op (terminalEtale Y)) :=
  (toConstantSheaf M).app _ m

/-- **The stalk of the constant sheaf is its value**: the germ of the constant section is a
bijection from `M` onto the stalk at a geometric point. -/
theorem bijective_germ_constSection (M : AddCommGrpCat.{u + 1}) :
    Function.Bijective (fun m : M => (Scheme.pointSmallEtale y).toPresheafFiber (terminalEtale Y)
      (terminalFiberPoint y) ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M).obj
      (constantSheafGlobalSection M m)) := by
  let Φ := Scheme.pointSmallEtale y
  have h := (Φ.toPresheafFiber_map_bijective (toConstantSheaf (Y := Y) M)).comp
    (bijective_toPresheafFiber_const y M (terminalEtale Y) (terminalFiberPoint y))
  have key : ∀ m : M, Φ.presheafFiber.map (toConstantSheaf (Y := Y) M)
      (Φ.toPresheafFiber (terminalEtale Y) (terminalFiberPoint y)
        ((Functor.const Y.Etaleᵒᵖ).obj M) m) =
      Φ.toPresheafFiber (terminalEtale Y) (terminalFiberPoint y)
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M).obj
        (constantSheafGlobalSection M m) := fun m =>
    Φ.toPresheafFiber_naturality_apply (toConstantSheaf (Y := Y) M) (terminalEtale Y)
      (terminalFiberPoint y) m
  exact ⟨fun a b hab => h.1 ((key a).trans (hab.trans (key b).symm)),
    fun q => (h.2 q).imp fun m hm => (key m).symm.trans hm⟩

end Point

/-! ### The torsor at a geometric point -/

section TorsorFibre

variable (M : AddCommGrpCat.{u + 1})
  (σ : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶
    (injectiveShortComplex ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)).X₃)

variable (Y) in
/-- The injective embedding of the constant sheaf `M`. -/
abbrev torsorSES : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  injectiveShortComplex ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)

variable (Y) in
/-- The global section of the injective sheaf attached to an element of `M`: the image of the
constant section. -/
def kernelSection (m : M) : (torsorSES Y M).X₂.obj.obj (op (terminalEtale Y)) :=
  (torsorSES Y M).f.hom.app _ (constantSheafGlobalSection M m)

/-- The section `kernelSection Y M m` maps to zero in the quotient. -/
theorem g_kernelSection (m : M) : (torsorSES Y M).g.hom.app _ (kernelSection Y M m) = 0 :=
  FibreSheaf.app_comp_apply_eq_zero _ _ (torsorSES Y M).zero _ _

/-- **Translation by an element of `M`**, acting on the torsor. -/
def torsorTranslate (m : M) : torsorSheaf M σ ⟶ torsorSheaf M σ :=
  FibreSheaf.translate.{u + 1} _ _ _ (kernelSection Y M m) (g_kernelSection M m)

/-- Translation by `m` adds the restriction of `kernelSection Y M m` to each section. -/
theorem torsorTranslate_app_coe (m : M) (U : Y.Etaleᵒᵖ) (t : (torsorSheaf M σ).obj.obj U) :
    FibreSheaf.toSec ((torsorTranslate M σ m).hom.app U t).1 =
      FibreSheaf.toSec t.1 + FibreSheaf.restr (terminalEtaleIsTerminal Y) (kernelSection Y M m)
        U.unop :=
  rfl

/-- Translation by `m + m'` is translation by `m` followed by translation by `m'`. -/
theorem torsorTranslate_add (m m' : M) :
    torsorTranslate M σ (m + m') = torsorTranslate M σ m ≫ torsorTranslate M σ m' := by
  have h : kernelSection Y M (m + m') = kernelSection Y M m + kernelSection Y M m' := by
    simp only [kernelSection, constantSheafGlobalSection, map_add]
    exact map_add (ConcreteCategory.hom ((torsorSES Y M).f.hom.app _)) _ _
  simp only [torsorTranslate, h]
  exact FibreSheaf.translate_add _ _ _ _ _ (g_kernelSection M m) (g_kernelSection M m')

/-- Translation by `0` is the identity. -/
theorem torsorTranslate_zero : torsorTranslate M σ 0 = 𝟙 _ := by
  have h : kernelSection Y M 0 = 0 := by
    rw [kernelSection, constantSheafGlobalSection, map_zero]
    exact map_zero (ConcreteCategory.hom ((torsorSES Y M).f.hom.app _))
  simp only [torsorTranslate, h, FibreSheaf.translate_zero]

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)

/-- **The stalk of the torsor at a geometric point is nonempty.** -/
theorem nonempty_presheafFiber_torsorSheaf :
    Nonempty ((Scheme.pointSmallEtale y).presheafFiber.obj (torsorSheaf M σ).obj) := by
  obtain ⟨Z, f, ⟨_, h, _, ⟨i⟩, -⟩, z, -⟩ := (Scheme.pointSmallEtale y).jointly_surjective _
    (FibreSheaf.exists_covering_nonempty.{u + 1} (torsorSES Y M).g (terminalEtaleIsTerminal Y)
      (sectionOfHom σ) (terminalEtale Y)) (terminalFiberPoint y)
  obtain ⟨t⟩ := i.2.2
  exact ⟨(Scheme.pointSmallEtale y).toPresheafFiber Z z (torsorSheaf M σ).obj
    ((torsorSheaf M σ).obj.map h.op t)⟩

/-- Restriction of the kernel section is the image of the restricted constant section. -/
theorem restr_kernelSection (m : M) (X : Y.Etale) :
    FibreSheaf.restr (terminalEtaleIsTerminal Y) (kernelSection Y M m) X =
      (torsorSES Y M).f.hom.app (op X)
        (FibreSheaf.restr (terminalEtaleIsTerminal Y)
          (constantSheafGlobalSection (Y := Y) M m) X) :=
  (NatTrans.naturality_apply (torsorSES Y M).f.hom _ _).symm

/-- **The translation action on the stalk of the torsor is free.** -/
theorem presheafFiber_torsorTranslate_injective
    (p : (Scheme.pointSmallEtale y).presheafFiber.obj (torsorSheaf M σ).obj) :
    Function.Injective fun m : M =>
      (Scheme.pointSmallEtale y).presheafFiber.map (torsorTranslate M σ m).hom p := by
  have hS := injectiveShortComplex_shortExact
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)
  obtain ⟨X, x, t, rfl⟩ :=
    (Scheme.pointSmallEtale y).toPresheafFiber_jointly_surjective (P := (torsorSheaf M σ).obj) p
  intro m m' h
  dsimp only at h
  rw [(Scheme.pointSmallEtale y).toPresheafFiber_naturality_apply,
    (Scheme.pointSmallEtale y).toPresheafFiber_naturality_apply] at h
  obtain ⟨Z, f, z, -, hf⟩ := ((Scheme.pointSmallEtale y).toPresheafFiber_eq_iff' X x _ _).1 h
  have h1 := congrArg (fun w : (torsorSheaf M σ).obj.obj (op Z) => FibreSheaf.toSec w.1) hf
  change (torsorSES Y M).X₂.obj.map f.op (FibreSheaf.toSec t.1 +
      FibreSheaf.restr (terminalEtaleIsTerminal Y) (kernelSection Y M m) X) =
    (torsorSES Y M).X₂.obj.map f.op (FibreSheaf.toSec t.1 +
      FibreSheaf.restr (terminalEtaleIsTerminal Y) (kernelSection Y M m') X) at h1
  rw [map_add, map_add, FibreSheaf.restr_map, FibreSheaf.restr_map, add_right_inj,
    restr_kernelSection, restr_kernelSection] at h1
  apply (bijective_germ_constSection y M).1
  change (Scheme.pointSmallEtale y).toPresheafFiber _ _
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M).obj
      (constantSheafGlobalSection (Y := Y) M m) =
    (Scheme.pointSmallEtale y).toPresheafFiber _ _
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M).obj
      (constantSheafGlobalSection (Y := Y) M m')
  rw [← fiber_map_terminal_eq y z ((terminalEtaleIsTerminal Y).from Z),
    ← (Scheme.pointSmallEtale y).toPresheafFiber_w_apply,
    ← (Scheme.pointSmallEtale y).toPresheafFiber_w_apply]
  exact congrArg _ (injective_app_of_shortExact hS (op Z) h1)

/-- **The translation action on the stalk of the torsor is simply transitive.** -/
theorem existsUnique_presheafFiber_torsorTranslate
    (p q : (Scheme.pointSmallEtale y).presheafFiber.obj (torsorSheaf M σ).obj) :
    ∃! m : M, (Scheme.pointSmallEtale y).presheafFiber.map (torsorTranslate M σ m).hom p = q := by
  have hS := injectiveShortComplex_shortExact
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)
  refine existsUnique_of_exists_of_unique ?_ fun m m' hm hm' =>
    presheafFiber_torsorTranslate_injective M σ y p (hm.trans hm'.symm)
  obtain ⟨X, x, t₁, t₂, rfl, rfl⟩ :=
    (Scheme.pointSmallEtale y).toPresheafFiber_jointly_surjective₂ (P := (torsorSheaf M σ).obj) p q
  have h₁ : (torsorSES Y M).g.hom.app (op X) (FibreSheaf.toSec t₁.1) =
      FibreSheaf.restr (terminalEtaleIsTerminal Y) (sectionOfHom σ) X := t₁.2
  have h₂ : (torsorSES Y M).g.hom.app (op X) (FibreSheaf.toSec t₂.1) =
      FibreSheaf.restr (terminalEtaleIsTerminal Y) (sectionOfHom σ) X := t₂.2
  obtain ⟨c, hc⟩ := exists_app_eq_of_shortExact hS (op X)
    (FibreSheaf.toSec t₂.1 - FibreSheaf.toSec t₁.1) (by rw [map_sub, h₁, h₂, sub_self])
  obtain ⟨m, hm⟩ := (bijective_germ_constSection y M).2
    ((Scheme.pointSmallEtale y).toPresheafFiber X x
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M).obj c)
  have hm' : (Scheme.pointSmallEtale y).toPresheafFiber X x
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M).obj
      (FibreSheaf.restr (terminalEtaleIsTerminal Y) (constantSheafGlobalSection (Y := Y) M m) X) =
      (Scheme.pointSmallEtale y).toPresheafFiber X x
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M).obj c := by
    refine Eq.trans ?_ hm
    rw [FibreSheaf.restr, (Scheme.pointSmallEtale y).toPresheafFiber_w_apply, fiber_map_terminal_eq]
  obtain ⟨Z, f, z, hz, hf⟩ := ((Scheme.pointSmallEtale y).toPresheafFiber_eq_iff' X x _ _).1 hm'
  refine ⟨m, ?_⟩
  rw [(Scheme.pointSmallEtale y).toPresheafFiber_naturality_apply, ← hz,
    ← (Scheme.pointSmallEtale y).toPresheafFiber_w_apply,
    ← (Scheme.pointSmallEtale y).toPresheafFiber_w_apply]
  congr 1
  refine Subtype.ext ?_
  change (torsorSES Y M).X₂.obj.map f.op (FibreSheaf.toSec t₁.1 +
      FibreSheaf.restr (terminalEtaleIsTerminal Y) (kernelSection Y M m) X) =
    (torsorSES Y M).X₂.obj.map f.op (FibreSheaf.toSec t₂.1)
  rw [show FibreSheaf.toSec t₂.1 = FibreSheaf.toSec t₁.1 + (torsorSES Y M).f.hom.app (op X) c by
    rw [hc, add_sub_cancel], map_add, map_add, restr_kernelSection]
  congr 1
  exact ((NatTrans.naturality_apply (torsorSES Y M).f.hom f.op _).symm.trans
    (congrArg (ConcreteCategory.hom ((torsorSES Y M).f.hom.app (op Z))) hf)).trans
      (NatTrans.naturality_apply (torsorSES Y M).f.hom f.op c)

end TorsorFibre

/-! ### Stalks of a representable sheaf -/

section Representable

variable {P : Sheaf Y.smallEtaleTopology (Type (u + 1))} {V : Y.Etale}
  (e : P ≅ (smallEtaleTopology Y).uliftYoneda.{u + 1}.obj V)

/-- The tautological section of a sheaf represented by `V`, over `V`. -/
def tautSection : P.obj.obj (op V) := e.inv.hom.app (op V) ⟨𝟙 V⟩

/-- The morphism to the representing object attached to a section. -/
def toHom {X : Y.Etale} (t : P.obj.obj (op X)) : X ⟶ V := (e.hom.hom.app (op X) t).down

/-- A section `t` over `X` is the pullback of the tautological section along `toHom e t`. -/
theorem map_toHom_tautSection {X : Y.Etale} (t : P.obj.obj (op X)) :
    P.obj.map (toHom e t).op (tautSection e) = t := by
  have h2 : e.inv.hom.app (op X) (e.hom.hom.app (op X) t) = t :=
    congrArg (fun φ : P ⟶ P => φ.hom.app (op X) t) e.hom_inv_id
  refine (NatTrans.naturality_apply e.inv.hom (toHom e t).op
    (⟨𝟙 V⟩ : ULift (V ⟶ V))).symm.trans (Eq.trans ?_ h2)
  congr 1

/-- The morphism attached to a restricted section is the composite with the restriction map. -/
theorem toHom_map {X X' : Y.Etale} (f : X ⟶ X') (t : P.obj.obj (op X')) :
    toHom e (P.obj.map f.op t) = f ≫ toHom e t :=
  congrArg ULift.down (NatTrans.naturality_apply e.hom.hom f.op t)

/-- The morphism attached to the tautological section is the identity of `V`. -/
theorem toHom_tautSection : toHom e (tautSection e) = 𝟙 V :=
  congrArg ULift.down (congrArg (fun φ : (smallEtaleTopology Y).uliftYoneda.{u + 1}.obj V ⟶
    (smallEtaleTopology Y).uliftYoneda.{u + 1}.obj V =>
      φ.hom.app (op V) (⟨𝟙 V⟩ : ULift (V ⟶ V))) e.inv_hom_id)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)

/-- **The stalk of a representable sheaf is the fibre of the representing object**: the germ of
the tautological section at a lift of the geometric point. -/
def germTaut (l : (Scheme.pointSmallEtale y).fiber.obj V) :
    (Scheme.pointSmallEtale y).presheafFiber.obj P.obj :=
  (Scheme.pointSmallEtale y).toPresheafFiber V l P.obj (tautSection e)

/-- The map `germTaut e y` from the fibre of `V` to the stalk of `P` is injective. -/
private theorem germTaut_injective : Function.Injective (germTaut e y) := by
  intro l l' h
  let φ : ∀ (X : Y.Etale) (_ : (Scheme.pointSmallEtale y).fiber.obj X),
      P.obj.obj (op X) ⟶ ULift.{u + 1} ((Scheme.pointSmallEtale y).fiber.obj V) :=
    fun X x => TypeCat.ofHom fun t =>
      ULift.up ((Scheme.pointSmallEtale y).fiber.map (toHom e t) x)
  have hφ : ∀ ⦃X X' : Y.Etale⦄ (f : X ⟶ X') (x : (Scheme.pointSmallEtale y).fiber.obj X),
      P.obj.map f.op ≫ φ X x = φ X' ((Scheme.pointSmallEtale y).fiber.map f x) := by
    intro X X' f x
    ext t
    change (Scheme.pointSmallEtale y).fiber.map (toHom e (P.obj.map f.op t)) x =
      (Scheme.pointSmallEtale y).fiber.map (toHom e t)
        ((Scheme.pointSmallEtale y).fiber.map f x)
    rw [toHom_map, Functor.map_comp_apply]
  let ψ := (Scheme.pointSmallEtale y).presheafFiberDesc φ hφ
  have key : ∀ l, ψ (germTaut e y l) = ULift.up l := by
    intro l
    refine (congrArg (fun g => g (tautSection e))
      ((Scheme.pointSmallEtale y).toPresheafFiber_presheafFiberDesc φ hφ V l)).trans ?_
    change ULift.up ((Scheme.pointSmallEtale y).fiber.map (toHom e (tautSection e)) l) = _
    rw [toHom_tautSection, Functor.map_id_apply]
  exact ULift.up_injective ((key l).symm.trans ((congrArg ψ h).trans (key l')))

/-- The map `germTaut e y` from the fibre of `V` to the stalk of `P` is surjective. -/
private theorem germTaut_surjective : Function.Surjective (germTaut e y) := by
  intro p
  obtain ⟨X, x, t, rfl⟩ := (Scheme.pointSmallEtale y).toPresheafFiber_jointly_surjective
    (P := P.obj) p
  refine ⟨(Scheme.pointSmallEtale y).fiber.map (toHom e t) x, ?_⟩
  rw [germTaut, ← (Scheme.pointSmallEtale y).toPresheafFiber_w_apply, map_toHom_tautSection]

/-- The map `germTaut e y` from the fibre of `V` to the stalk of `P` is bijective. -/
theorem bijective_germTaut : Function.Bijective (germTaut e y) :=
  ⟨germTaut_injective e y, germTaut_surjective e y⟩

/-- **Endomorphisms of a representable sheaf act on the stalk as their representing
endomorphisms act on the fibre.** -/
theorem presheafFiber_map_germTaut (τ : P ⟶ P) (l : (Scheme.pointSmallEtale y).fiber.obj V) :
    (Scheme.pointSmallEtale y).presheafFiber.map τ.hom (germTaut e y l) =
      germTaut e y ((Scheme.pointSmallEtale y).fiber.map (toHom e (τ.hom.app _ (tautSection e)))
        l) := by
  rw [germTaut, (Scheme.pointSmallEtale y).toPresheafFiber_naturality_apply, germTaut,
    ← (Scheme.pointSmallEtale y).toPresheafFiber_w_apply, map_toHom_tautSection]

end Representable

/-! ### The torsor cover -/

/-- **A class in `H^1` with finite constant coefficients dies on a torsor cover.** Let `M` be a
finite abelian group and `ζ ∈ H^1(Y, M)`. There is a finite étale `Y`-scheme `V` with an action
`m ↦ α m` of `M` by endomorphisms over `Y` such that `ζ` restricts to zero on `V` and, at every
geometric point of `Y`, the action of `M` on the geometric fibre of `V` is free and transitive
and the fibre is nonempty: `V` is an `M`-torsor, the one attached to `ζ` by [Stacks, Tag 03AJ]
and [Stacks, Tag 03RV]. -/
theorem exists_torsorCover (M : AddCommGrpCat.{u + 1}) [Finite M]
    (ζ : Sheaf.H.{u + 1} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) 1) :
    ∃ (V : Y.Etale) (α : M → (V ⟶ V)), IsFinite V.hom ∧
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} V.hom _ 1 ζ = 0 ∧
      (∀ m m', α (m + m') = α m ≫ α m') ∧ α 0 = 𝟙 V ∧
      ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y),
        Nonempty ((Scheme.pointSmallEtale y).fiber.obj V) ∧
          ∀ l l' : (Scheme.pointSmallEtale y).fiber.obj V,
            ∃! m : M, (Scheme.pointSmallEtale y).fiber.map (α m) l = l' := by
  have hS := injectiveShortComplex_shortExact
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)
  obtain ⟨σ, hσ⟩ := exists_eq_comp_extClass_of_injective hS ζ
  obtain ⟨V, hV, ⟨e⟩⟩ := exists_isFinite_iso_uliftYoneda M σ
  let α : M → (V ⟶ V) := fun m => toHom e ((torsorTranslate M σ m).hom.app _ (tautSection e))
  have hα : ∀ m m', α (m + m') = α m ≫ α m' := by
    intro m m'
    change toHom e ((torsorTranslate M σ (m + m')).hom.app _ (tautSection e)) = _
    rw [torsorTranslate_add]
    change toHom e ((torsorTranslate M σ m').hom.app _
      ((torsorTranslate M σ m).hom.app _ (tautSection e))) = _
    rw [← map_toHom_tautSection e ((torsorTranslate M σ m).hom.app _ (tautSection e))]
    exact (congrArg (toHom e) (NatTrans.naturality_apply (torsorTranslate M σ m').hom _ _)).trans
      (toHom_map e _ _)
  refine ⟨V, α, hV, ?_, hα, ?_, fun y => ⟨?_, fun l l' => ?_⟩⟩
  · rw [← hσ]
    exact etaleCohomologyRestrictionMap_comp_extClass_eq_zero hS σ V
      (FibreSheaf.toSec (tautSection e).1) (tautSection e).2
  · change toHom e ((torsorTranslate M σ 0).hom.app _ (tautSection e)) = _
    rw [torsorTranslate_zero]
    exact toHom_tautSection e
  · obtain ⟨p⟩ := nonempty_presheafFiber_torsorSheaf M σ y
    obtain ⟨l, -⟩ := (bijective_germTaut e y).2 p
    exact ⟨l⟩
  · obtain ⟨m, hm, huniq⟩ := existsUnique_presheafFiber_torsorTranslate M σ y
      (germTaut e y l) (germTaut e y l')
    exact ⟨m, (bijective_germTaut e y).1 ((presheafFiber_map_germTaut e y _ l).symm.trans hm),
      fun m' hm' => huniq m' ((presheafFiber_map_germTaut e y _ l).trans
        (congrArg (germTaut e y) hm'))⟩

end Stacks.EtaleCohomology

end
