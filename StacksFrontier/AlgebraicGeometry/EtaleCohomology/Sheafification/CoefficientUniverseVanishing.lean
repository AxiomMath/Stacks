module

public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjectiveSmallSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleLocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.UliftFunctorSheafification
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftCohomology

/-!
# Enlarging the coefficient universe of étale cohomology

Let `X` be a scheme in `Scheme.{u}`. Abelian sheaves on `X_étale` can be taken with sections in
`AddCommGrpCat.{u + 1}` or in any larger `AddCommGrpCat.{max (u + 1) v}`. This file shows that a
vanishing statement for the étale cohomology of torsion sheaves passes from the smallest
coefficient universe to every larger one, on a quasi-compact quasi-separated scheme.

## Main results

* `Stacks.EtaleCohomology.SmallSubpresheaf` — the subpresheaves of an abelian sheaf `F` all of
  whose groups of sections are `u`-small; `F` is the filtered colimit of their sheafifications
  (`Stacks.EtaleCohomology.smallSubpresheafSheafCoconeIsColimit`), and each of those is the
  universe lift of a sheaf with sections in `AddCommGrpCat.{u + 1}`
  (`Stacks.EtaleCohomology.smallSubpresheafSheafIso`).
* `Stacks.EtaleCohomology.preservesInjectiveObjects_uliftSheafFunctor_smallEtale_of_univLE` —
  the universe lift of abelian sheaves on `X_étale` preserves injective objects.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_forall_subsingleton_sheafH_univ` — **the
  comparison**: if `H^q(X, G) = 0` for every torsion sheaf `G` with sections in
  `AddCommGrpCat.{u + 1}`, then `H^q(X, F) = 0` for every torsion sheaf `F` with sections in
  `AddCommGrpCat.{max (u + 1) v}`.

## Implementation notes

The comparison is the composite of three facts. Cohomology is unchanged by the universe lift
(`Stacks.Sheaves.UniverseLift.subsingleton_sheafH_uliftSheafFunctor_iff`, from the exactness of
the lift and its preservation of injective objects). A torsion sheaf `F` of the larger universe
is the filtered colimit of the sheafifications of its small subpresheaves, which are universe
lifts of torsion sheaves of the smaller universe. Étale cohomology of a quasi-compact
quasi-separated scheme commutes with filtered colimits (Stacks 03Q5,
`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale`).

## References

* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.UniverseLift AlgebraicGeometry AlgebraicGeometry.Scheme

universe v₀ v u

namespace Stacks.EtaleCohomology

/-- **On the small étale site the universe lift preserves injective abelian sheaves**, starting
from any coefficient universe `max (u + 1) v₀`. The site is essentially small in that universe;
on a small model the statement is
`Stacks.Cohomology.CoefficientLowering.sheafCompose_preservesInjectiveObjects`, and restriction
along the small model is an equivalence of sheaf categories in both coefficient universes.
(`AlgebraicGeometry.Scheme.preservesInjectiveObjects_uliftSheafFunctor_smallEtale` is the case of
coefficients in `AddCommGrpCat.{u}`.) -/
theorem preservesInjectiveObjects_uliftSheafFunctor_smallEtale_of_univLE (X : Scheme.{u}) :
    (uliftSheafFunctor.{v, max (u + 1) v₀} X.smallEtaleTopology).PreservesInjectiveObjects := by
  let e := equivSmallModel.{max (u + 1) v₀} X.Etale
  let J₀ := e.inverse.inducedTopology X.smallEtaleTopology
  let : EssentiallySmall.{max (max (u + 1) v₀) v} (SmallModel.{max (u + 1) v₀} X.Etale) :=
    essentiallySmall_lift.{v, max (u + 1) v₀} _
  let : HasSheafify J₀ AddCommGrpCat.{max (max (u + 1) v₀) v} :=
    hasSheafify_addCommGrpCat_of_essentiallySmall.{max (max (u + 1) v₀) v} J₀
  let : HasSheafify J₀ AddCommGrpCat.{max (u + 1) v₀} :=
    hasSheafify_addCommGrpCat_of_essentiallySmall.{max (u + 1) v₀} J₀
  have : AddCommGrpCat.uliftFunctor.{v, max (u + 1) v₀}.PreservesInjectiveObjects :=
    preservesInjectiveObjects_addCommGrpCat_uliftFunctor.{v, max (u + 1) v₀}
  have h : (uliftSheafFunctor.{v, max (u + 1) v₀} J₀).PreservesInjectiveObjects :=
    Stacks.Cohomology.CoefficientLowering.sheafCompose_preservesInjectiveObjects J₀
      AddCommGrpCat.uliftFunctor.{v, max (u + 1) v₀}
  have : (e.inverse.sheafPushforwardContinuous AddCommGrpCat.{max (max (u + 1) v₀) v} J₀
      X.smallEtaleTopology).IsEquivalence :=
    have : ∀ Y, HasLimitsOfShape (StructuredArrow Y e.inverse.op)
        AddCommGrpCat.{max (max (u + 1) v₀) v} := fun _ ↦ inferInstance
    inferInstance
  have : (e.inverse.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v₀} J₀
      X.smallEtaleTopology).IsEquivalence :=
    have : ∀ Y, HasLimitsOfShape (StructuredArrow Y e.inverse.op)
        AddCommGrpCat.{max (u + 1) v₀} := fun _ ↦ inferInstance
    inferInstance
  exact preservesInjectiveObjects_uliftSheafFunctor_of_isEquivalence.{v, max (u + 1) v₀} e.inverse
    J₀ X.smallEtaleTopology h

/-! ### Shrinking and the universe lift -/

/-- **The universe lift of `Stacks.shrinkPresheaf P` is `P`**: a presheaf of abelian groups whose
groups of sections are all `m`-small is the universe lift of a presheaf of abelian groups with
sections in `Type m`. -/
def _root_.Stacks.shrinkPresheafUliftIso.{m, t, u₁, v₁} {C : Type u₁} [Category.{v₁} C]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max m t}) [∀ U, Small.{m} (P.obj U)] :
    Stacks.shrinkPresheaf.{m, t} P ⋙ AddCommGrpCat.uliftFunctor.{t, m} ≅ P :=
  NatIso.ofComponents
    (fun U ↦ (AddEquiv.ulift.trans (Shrink.addEquiv (α := (P.obj U : Type _)))).toAddCommGrpIso)
    (fun {U V} φ ↦ by
      ext y
      exact Stacks.shrinkPresheaf_map_apply.{m, t} P φ y.down)

/-! ### Small subpresheaves -/

section SmallSubpresheaves

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})

/-- The families of subgroups of the sections of `F`, stable under restriction, all of whose
groups are `u`-small. Ordered by inclusion, they form a directed set. -/
abbrev SmallSubpresheaf :=
  {S : ∀ U : X.Etaleᵒᵖ, AddSubgroup (F.obj.obj U) //
    (∀ ⦃U V : X.Etaleᵒᵖ⦄ (φ : U ⟶ V) (x : F.obj.obj U), x ∈ S U → (F.obj.map φ).hom x ∈ S V) ∧
      ∀ U, Small.{u} (S U)}

/-- Small subpresheaves of `F` are ordered by inclusion of their subgroups of sections. -/
instance : PartialOrder (SmallSubpresheaf F) := Subtype.partialOrder _

namespace SmallSubpresheaf

variable {F}

/-- The family of subgroups generated by one section. -/
def generated {U₀ : X.Etaleᵒᵖ} (x : F.obj.obj U₀) : SmallSubpresheaf F := by
  refine ⟨fun V ↦ AddSubgroup.closure (Set.range fun φ : U₀ ⟶ V ↦ (F.obj.map φ).hom x),
    fun U V ψ y hy ↦ ?_, fun V ↦ ?_⟩
  · have hle : AddSubgroup.closure (Set.range fun φ : U₀ ⟶ U ↦ (F.obj.map φ).hom x) ≤
        (AddSubgroup.closure (Set.range fun φ : U₀ ⟶ V ↦ (F.obj.map φ).hom x)).comap
          (F.obj.map ψ).hom := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨φ, rfl⟩
      exact AddSubgroup.subset_closure ⟨φ ≫ ψ, by simp⟩
    exact hle hy
  · let g := FreeAbelianGroup.lift (fun φ : U₀ ⟶ V ↦ (F.obj.map φ).hom x)
    have hsub : (AddSubgroup.closure (Set.range fun φ : U₀ ⟶ V ↦ (F.obj.map φ).hom x) :
        Set (F.obj.obj V)) ⊆ Set.range g := by
      rw [← AddMonoidHom.coe_range, SetLike.coe_subset_coe, AddSubgroup.closure_le]
      rintro _ ⟨φ, rfl⟩
      exact ⟨FreeAbelianGroup.of φ, by simp [g]⟩
    have : Small.{u} (Set.range g) := small_range _
    exact small_subset hsub

/-- A section `x` lies in the family of subgroups it generates. -/
theorem mem_generated {U₀ : X.Etaleᵒᵖ} (x : F.obj.obj U₀) :
    x ∈ (generated x).1 U₀ :=
  AddSubgroup.subset_closure ⟨𝟙 U₀, by simp⟩

/-- The pointwise sum of two families. -/
def sup (S T : SmallSubpresheaf F) : SmallSubpresheaf F := by
  refine ⟨fun U ↦ S.1 U ⊔ T.1 U, fun U V φ y hy ↦ ?_, fun U ↦ ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hy
    rw [map_add]
    exact AddSubgroup.add_mem_sup (S.2.1 φ a ha) (T.2.1 φ b hb)
  · have := S.2.2 U
    have := T.2.2 U
    refine small_of_surjective (f := fun p : S.1 U × T.1 U ↦
      (⟨p.1.1 + p.2.1, AddSubgroup.add_mem_sup p.1.2 p.2.2⟩ : ↥(S.1 U ⊔ T.1 U))) ?_
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hy
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

/-- Any two small subpresheaves of `F` are contained in a third, their pointwise sum. -/
instance : IsDirected (SmallSubpresheaf F) (· ≤ ·) where
  directed S T := ⟨sup S T, fun U ↦ le_sup_left (a := S.1 U), fun U ↦ le_sup_right (b := T.1 U)⟩

/-- The zero family is a small subpresheaf of `F`. -/
instance : Nonempty (SmallSubpresheaf F) :=
  ⟨⟨fun _ ↦ ⊥,
    fun U V φ y hy ↦ by
      rw [AddSubgroup.mem_bot] at hy ⊢
      rw [hy, map_zero],
    fun _ ↦ by
      change Small.{u} (⊥ : AddSubgroup _)
      infer_instance⟩⟩

/-- The restriction maps of a family of subgroups. -/
def restrict (S : SmallSubpresheaf F) {U V : X.Etaleᵒᵖ} (φ : U ⟶ V) : S.1 U →+ S.1 V :=
  ((F.obj.map φ).hom.comp (S.1 U).subtype).codRestrict (S.1 V) fun y ↦ S.2.1 φ _ y.2

/-- The restriction map of `S` is the restriction map of `F` on elements of `S`. -/
@[simp]
theorem coe_restrict (S : SmallSubpresheaf F) {U V : X.Etaleᵒᵖ} (φ : U ⟶ V) (y : S.1 U) :
    (S.restrict φ y : F.obj.obj V) = (F.obj.map φ).hom y := rfl

/-- Restriction along the identity is the identity. -/
@[simp]
theorem restrict_id (S : SmallSubpresheaf F) (U : X.Etaleᵒᵖ) (y : S.1 U) :
    S.restrict (𝟙 U) y = y :=
  Subtype.ext (by simp)

/-- Restriction along a composite is the composite of the restrictions. -/
@[simp]
theorem restrict_comp (S : SmallSubpresheaf F) {U V W : X.Etaleᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)
    (y : S.1 U) : S.restrict (φ ≫ ψ) y = S.restrict ψ (S.restrict φ y) :=
  Subtype.ext (by simp)

/-- The presheaf of abelian groups of a family of subgroups. -/
def presheaf (S : SmallSubpresheaf F) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} where
  obj U := AddCommGrpCat.of (S.1 U)
  map φ := AddCommGrpCat.ofHom (S.restrict φ)
  map_id U := by ext y; simp
  map_comp φ ψ := by ext y; simp

/-- The inclusion of the presheaf of a family into `F`. -/
def ι (S : SmallSubpresheaf F) : S.presheaf ⟶ F.obj where
  app U := AddCommGrpCat.ofHom (S.1 U).subtype
  naturality U V φ := by ext y; rfl

end SmallSubpresheaf

/-- The diagram of the presheaves of the small subpresheaves of `F`. -/
def smallSubpresheafDiagram : SmallSubpresheaf F ⥤ X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} where
  obj S := S.presheaf
  map {S T} h :=
    { app U := AddCommGrpCat.ofHom (AddSubgroup.inclusion (leOfHom h U))
      naturality U V φ := by ext y; rfl }

/-- The cocone of the small subpresheaves of `F`, with vertex the underlying presheaf of `F`. -/
def smallSubpresheafCocone : Cocone (smallSubpresheafDiagram F) where
  pt := F.obj
  ι := { app S := S.ι }

/-- **The underlying presheaf of `F` is the filtered union of its small subpresheaves.** -/
def smallSubpresheafCoconeIsColimit : IsColimit (smallSubpresheafCocone F) := by
  refine evaluationJointlyReflectsColimits _ fun U ↦ ?_
  have : ReflectsColimitsOfShape (SmallSubpresheaf F) (forget AddCommGrpCat.{max (u + 1) v}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget AddCommGrpCat.{max (u + 1) v})
  apply Types.FilteredColimit.isColimitOf'
  · exact fun y ↦ ⟨SmallSubpresheaf.generated y, ⟨y, SmallSubpresheaf.mem_generated y⟩, rfl⟩
  · exact fun S y z h ↦ ⟨S, 𝟙 S, congrArg _ (Subtype.ext h : y = z)⟩

namespace SmallSubpresheaf

variable {F}

/-- The groups of sections of the presheaf of a small subpresheaf are `(u + 1)`-small. -/
instance small_presheaf_obj (S : SmallSubpresheaf F) (U : X.Etaleᵒᵖ) :
    Small.{u + 1} (S.presheaf.obj U) :=
  have := S.2.2 U
  Small.mk' ((equivShrink.{u} (S.1 U)).trans Equiv.ulift.{u + 1, u}.symm)

/-- The presheaf of a small subpresheaf, with its groups replaced by isomorphic groups in
`Type (u + 1)`: `Stacks.shrinkPresheaf`. -/
abbrev shrinkPresheaf (S : SmallSubpresheaf F) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Stacks.shrinkPresheaf.{u + 1, v} S.presheaf

/-- A small subpresheaf of a torsion sheaf is locally torsion. -/
theorem isLocallyTorsion_shrinkPresheaf
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (S : SmallSubpresheaf F) :
    Stacks.Torsion.IsLocallyTorsion X.smallEtaleTopology S.shrinkPresheaf := by
  intro U y
  obtain ⟨R, hR, hkill⟩ :=
    (Stacks.Torsion.torsionSheafProperty_iff_isLocallyTorsion _ F).1 hF U
      (Shrink.addEquiv (α := (S.presheaf.obj (Opposite.op U) : Type _)) y).1
  refine ⟨R, hR, fun V φ hφ ↦ ?_⟩
  obtain ⟨n, hn, hz⟩ := hkill V φ hφ
  refine ⟨n, hn, (Shrink.addEquiv (α := (S.presheaf.obj (Opposite.op V) : Type _))).injective ?_⟩
  calc Shrink.addEquiv (n • (S.shrinkPresheaf.map φ.op).hom y)
      _ = n • Shrink.addEquiv ((S.shrinkPresheaf.map φ.op).hom y) := map_nsmul _ _ _
      _ = n • (S.presheaf.map φ.op).hom (Shrink.addEquiv y) := by
        rw [Stacks.shrinkPresheaf_map_apply.{u + 1, v} S.presheaf φ.op y]
      _ = 0 := Subtype.ext hz
      _ = Shrink.addEquiv 0 := (map_zero _).symm

end SmallSubpresheaf

/-- The diagram of the sheafifications of the small subpresheaves of `F`. -/
abbrev smallSubpresheafSheafDiagram :
    SmallSubpresheaf F ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  smallSubpresheafDiagram F ⋙ presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}

/-- The cocone of the sheafifications of the small subpresheaves of `F`, with vertex `F`. -/
abbrev smallSubpresheafSheafCocone : Cocone (smallSubpresheafSheafDiagram F) :=
  ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).mapCocone
    (smallSubpresheafCocone F)).extend
      ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).counit.app F)

/-- **Every abelian sheaf is the filtered colimit of the sheafifications of its small
subpresheaves.** -/
def smallSubpresheafSheafCoconeIsColimit : IsColimit (smallSubpresheafSheafCocone F) :=
  IsColimit.ofIsoColimit (isColimitOfPreserves _ (smallSubpresheafCoconeIsColimit F))
    (Cocone.extendIso ((presheafToSheaf X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).mapCocone (smallSubpresheafCocone F))
      (@asIso _ _ _ _ ((sheafificationAdjunction X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).counit.app F) (isIso_sheafificationAdjunction_counit F)))

/-- The sheafification of a small subpresheaf is the universe lift of an abelian sheaf with
sections in `AddCommGrpCat.{u + 1}`. -/
def smallSubpresheafSheafIso (S : SmallSubpresheaf F) :
    (uliftSheafFunctor.{v, u + 1} X.smallEtaleTopology).obj
        ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj S.shrinkPresheaf) ≅
      (smallSubpresheafSheafDiagram F).obj S :=
  haveI : X.smallEtaleTopology.PreservesSheafification AddCommGrpCat.uliftFunctor.{v, u + 1} :=
    preservesSheafification_uliftFunctor.{u + 1, u, u + 1, v}
  ((sheafComposeNatIso X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{v, u + 1}
      (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})).app
        S.shrinkPresheaf).symm ≪≫
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).mapIso
      (Stacks.shrinkPresheafUliftIso.{u + 1, v} S.presheaf)

end SmallSubpresheaves

/-! ### The comparison -/

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- **Vanishing of étale cohomology of torsion sheaves passes to every coefficient universe.**
Let `X` be a quasi-compact and quasi-separated scheme and `q` a degree. If `H^q(X, G) = 0` for
every torsion abelian sheaf `G` on `X_étale` with sections in `AddCommGrpCat.{u + 1}`, then
`H^q(X, F) = 0` for every torsion abelian sheaf `F` with sections in
`AddCommGrpCat.{max (u + 1) v}`.

The sheaf `F` is the filtered colimit of the sheafifications of its small subpresheaves
(`smallSubpresheafSheafCoconeIsColimit`), each the universe lift of a torsion sheaf of the
smaller universe (`smallSubpresheafSheafIso`, `SmallSubpresheaf.isLocallyTorsion_shrinkPresheaf`),
whose cohomology is that of the sheaf it lifts
(`Stacks.Sheaves.UniverseLift.subsingleton_sheafH_uliftSheafFunctor_iff`); cohomology commutes
with filtered colimits on a quasi-compact quasi-separated scheme (Stacks 03Q5,
`isIso_colimit_post_rightDerived_Γ_smallEtale`). -/
theorem subsingleton_sheafH_of_forall_subsingleton_sheafH_univ (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (q : ℕ)
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (h : ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
        Subsingleton (Sheaf.H.{u + 1} G q))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    Subsingleton (Sheaf.H.{max (u + 1) v} F q) := by
  let R := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived q
  have : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    wEqualsLocallyBijective_smallEtaleTopology.{u, 0} X
  have : (uliftSheafFunctor.{v, u + 1} X.smallEtaleTopology).PreservesInjectiveObjects :=
    preservesInjectiveObjects_uliftSheafFunctor_smallEtale_of_univLE.{0, v} X
  have hpiece : ∀ S : SmallSubpresheaf F,
      IsZero (R.obj ((smallSubpresheafSheafDiagram F).obj S)) := by
    intro S
    have hG : Stacks.Torsion.torsionSheafProperty.{u + 1, u, u + 1} X.smallEtaleTopology
        ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj S.shrinkPresheaf) :=
      Stacks.Torsion.torsionSheafProperty_sheafify X.smallEtaleTopology S.shrinkPresheaf
        (S.isLocallyTorsion_shrinkPresheaf hF)
    exact ((Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{v, u,
      u + 1} X.smallEtaleTopology _ q).1
        ((subsingleton_sheafH_uliftSheafFunctor_iff.{u + 1, max (u + 1) v, v, u + 1}
          X.smallEtaleTopology _ q).2 (h _ hG))).of_iso
      (R.mapIso (smallSubpresheafSheafIso F S)).symm
  have hcolim : IsZero (colimit (smallSubpresheafSheafDiagram F ⋙ R)) :=
    (IsZero.iff_id_eq_zero _).2 (colimit.hom_ext fun S ↦ (hpiece S).eq_of_src _ _)
  have := isIso_colimit_post_rightDerived_Γ_smallEtale.{v} X q (smallSubpresheafSheafDiagram F)
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{v, u,
    u + 1} X.smallEtaleTopology F q).2
      ((hcolim.of_iso (asIso (colimit.post (smallSubpresheafSheafDiagram F) R)).symm).of_iso
        (R.mapIso ((colimit.isColimit _).coconePointUniqueUpToIso
          (smallSubpresheafSheafCoconeIsColimit F))).symm)

/-- **The cohomological dimension bound for proper curves, at every coefficient universe.** If
`H^q(C, G) = 0` for `q > 2`, every proper scheme `C` of dimension at most one over an
algebraically closed field and every torsion abelian sheaf `G` on `C_étale` with sections in
`AddCommGrpCat.{u + 1}` (clause (1) of [Stacks, Tag 03SC] at the smallest coefficient universe),
then the same holds for torsion abelian sheaves with sections in `AddCommGrpCat.{max (u + 1) v}`.
This is `subsingleton_sheafH_of_forall_subsingleton_sheafH_univ`, a proper scheme over a field
being quasi-compact and quasi-separated. -/
theorem subsingleton_sheafH_of_isProper_of_isAlgClosed_of_curve_univ
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      (π : X ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞) →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
        Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
        ∀ q : ℕ, 2 * 1 < q →
          letI := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X
          letI := IsGrothendieckAbelian.hasExt.{u + 1}
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          Subsingleton (Sheaf.H.{u + 1} G q))
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    (π : X ⟶ Spec (.of k)) [IsProper π] (hX : topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) (q : ℕ) (hq : 2 * 1 < q) :
    letI := isGrothendieckAbelian_sheaf_smallEtale.{u, v} X
    letI := IsGrothendieckAbelian.hasExt.{max (u + 1) v}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    Subsingleton (Sheaf.H.{max (u + 1) v} G q) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated π
  let := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X
  let := IsGrothendieckAbelian.hasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  let := isGrothendieckAbelian_sheaf_smallEtale.{u, v} X
  let := IsGrothendieckAbelian.hasExt.{max (u + 1) v}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  exact subsingleton_sheafH_of_forall_subsingleton_sheafH_univ.{v} X q
    (fun G' hG' ↦ h k X π hX G' hG' q hq) G hG

end Stacks.EtaleCohomology

end
