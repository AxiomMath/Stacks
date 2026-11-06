module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksFrontier.Algebra.Homology.Resolution.MapInjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing

/-!
# Higher direct images through section complexes, and local vanishing

Let `u : D ⥤ C` be a continuous functor from a site `(D, J)` to a site `(C, K)`, so that it
induces the direct image `u_*` on abelian sheaves. For an abelian sheaf `F` on `C` with an
injective resolution `I`, write `Γ(I)` for the complex of section presheaves of `I` and
`u^p Γ(I)` for its restriction along `u`. This file records

`R^p u_* F ≅ a_J (H^p(u^p Γ(I)))`

(the abelian form of Stacks 072W, through a chosen resolution), and the two consequences that
are used to prove vanishing of a higher direct image by working locally on the target:

* `R^p u_* F = 0` exactly when every section of the presheaf `H^p(u^p Γ(I))` dies on a
  `J`-covering sieve;
* local death of sections can be transported along a functor `Ψ : C₀ ⥤ D` of sites, provided
  restriction along `Ψ ⋙ u` is exact and preserves injective objects and `Ψ` preserves covers:
  it suffices that the sections of the corresponding presheaf for the restricted sheaf
  `(Ψ ⋙ u)^* F` and the restricted resolution die locally on `C₀`.

## Main definitions

* `Stacks.Cohomology.SectionComplexVanishing.pushforwardSections`: the complex `u^p Γ(I)`.

## Main results

* `Stacks.Cohomology.SectionComplexVanishing.rightDerivedPushforwardIso`: `R^p u_* F` is the
  `J`-sheafification of `H^p(u^p Γ(I))`.
* `Stacks.Cohomology.SectionComplexVanishing.isZero_rightDerived_of_locallyZero` and
  `Stacks.Cohomology.SectionComplexVanishing.equalizerSieve_mem_of_isZero_rightDerived`: the two
  directions of the local vanishing criterion.
* `Stacks.Cohomology.SectionComplexVanishing.equalizerSieve_mem_of_restriction`: the transport of
  local vanishing along `Ψ`.

## Implementation notes

The section complexes, rather than cohomology computed through `Ext` or through right derived
functors of sections, are used because they make all the naturality in the object automatic:
`H^p(u^p Γ(I))` is a presheaf, and restricting the resolution along an exact functor which
preserves injective objects gives an injective resolution
(`CategoryTheory.InjectiveResolution.mapOfPreservesInjectives`) whose section complex is the
restricted section complex on the nose. Nothing is assumed about the universes of the two sites
beyond the existence of the sheafifications and injective resolutions involved.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

universe t u₁ v₁ u₂ v₂ u₀ v₀

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.SectionComplexVanishing

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology D) (K : GrothendieckTopology C) (u : D ⥤ C) [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]

/-- The complex of section presheaves of an injective resolution `I` of an abelian sheaf on `C`,
restricted along `u : D ⥤ C`: the complex of presheaves `V ↦ I^•(u V)` on `D`. -/
abbrev pushforwardSections {F : Sheaf K AddCommGrpCat.{t}} (I : InjectiveResolution F) :
    CochainComplex (Dᵒᵖ ⥤ AddCommGrpCat.{t}) ℕ :=
  ((sheafToPresheaf J AddCommGrpCat.{t}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (((u.sheafPushforwardContinuous AddCommGrpCat.{t} J K).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)

variable [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{t})]

/-- **Stacks 072W for abelian sheaves, through a resolution.** The `p`-th higher direct image
`R^p u_* F` is the `J`-sheafification of the `p`-th homology presheaf of the restricted section
complex of an injective resolution `I` of `F`. -/
def rightDerivedPushforwardIso {F : Sheaf K AddCommGrpCat.{t}} (I : InjectiveResolution F)
    (p : ℕ) :
    ((u.sheafPushforwardContinuous AddCommGrpCat.{t} J K).rightDerived p).obj F ≅
      (presheafToSheaf J AddCommGrpCat.{t}).obj ((pushforwardSections J K u I).homology p) := by
  let T := u.sheafPushforwardContinuous AddCommGrpCat.{t} J K
  let A := presheafToSheaf J AddCommGrpCat.{t}
  let L := (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let P := pushforwardSections J K u I
  have ecpx : (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj P ≅ L :=
    ((NatIso.mapHomologicalComplex (sheafificationNatIso J AddCommGrpCat.{t})
        (ComplexShape.up ℕ)).app L).symm ≪≫
      (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℕ)).app L
  exact (I.isoRightDerivedObj T p).trans
    ((((P.sc p).mapHomologyIso A).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).mapIso ecpx).symm)

/-- **A higher direct image vanishes when the sections of its homology presheaf die locally.** -/
theorem isZero_rightDerived_of_locallyZero [J.HasSheafCompose (forget AddCommGrpCat.{t})]
    {F : Sheaf K AddCommGrpCat.{t}} (I : InjectiveResolution F) (p : ℕ)
    (h : ∀ (V : D) (x : ToType ((((pushforwardSections J K u I).homology p)).obj (op V))),
      Presheaf.equalizerSieve (X := op V) x 0 ∈ J V) :
    IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{t} J K).rightDerived p).obj F) :=
  (SheafifiedHigherDirectImage.isZero_presheafToSheaf_of_locallyZero J _ h).of_iso
    (rightDerivedPushforwardIso J K u I p)

/-- **Conversely, when a higher direct image vanishes, the sections of its homology presheaf die
locally**: the unit of sheafification is locally injective, and a section and zero have the same
image in the zero group of sections of the sheafification. -/
theorem equalizerSieve_mem_of_isZero_rightDerived
    [∀ P : Dᵒᵖ ⥤ AddCommGrpCat.{t},
      Presheaf.IsLocallyInjective J (toSheafify J P)]
    {F : Sheaf K AddCommGrpCat.{t}} (I : InjectiveResolution F) (p : ℕ)
    (hz : IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{t} J K).rightDerived p).obj F))
    (V : D) (x : ToType ((((pushforwardSections J K u I).homology p)).obj (op V))) :
    Presheaf.equalizerSieve (X := op V) x 0 ∈ J V := by
  let P := (pushforwardSections J K u I).homology p
  have hsub : Subsingleton (ToType ((sheafify J P).obj (op V))) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp
      ((sheafToPresheaf J AddCommGrpCat.{t} ⋙
          (evaluation Dᵒᵖ AddCommGrpCat.{t}).obj (op V)).map_isZero
        (hz.of_iso (rightDerivedPushforwardIso J K u I p).symm))
  exact Presheaf.equalizerSieve_mem J (toSheafify J P) x 0 (hsub.allEq _ _)

end Pushforward

section Transport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C₀ : Type u₀} [Category.{v₀} C₀]
  (J : GrothendieckTopology D) (K : GrothendieckTopology C) (u : D ⥤ C) [u.IsContinuous J K]
  (J₀ K₀ : GrothendieckTopology C₀) (Ψ : C₀ ⥤ D) [(Ψ ⋙ u).IsContinuous K₀ K]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  [HasSheafify J₀ AddCommGrpCat.{t}] [HasSheafify K₀ AddCommGrpCat.{t}]
  [(𝟭 C₀).IsContinuous J₀ K₀]
  [((Ψ ⋙ u).sheafPushforwardContinuous AddCommGrpCat.{t} K₀ K).Additive]
  [((Ψ ⋙ u).sheafPushforwardContinuous AddCommGrpCat.{t} K₀ K).PreservesHomology]
  [((Ψ ⋙ u).sheafPushforwardContinuous AddCommGrpCat.{t} K₀ K).PreservesInjectiveObjects]

/-- The restriction along `Ψ ⋙ u` of an injective resolution of `F`: an injective resolution of
the restriction of `F`. -/
abbrev restrictedResolution {F : Sheaf K AddCommGrpCat.{t}} (I : InjectiveResolution F) :
    InjectiveResolution (((Ψ ⋙ u).sheafPushforwardContinuous AddCommGrpCat.{t} K₀ K).obj F) :=
  I.mapOfPreservesInjectives ((Ψ ⋙ u).sheafPushforwardContinuous AddCommGrpCat.{t} K₀ K)

/-- The homology presheaf of the restricted section complex of `I`, further restricted along
`Ψ`, is the homology presheaf of the section complex of the restricted resolution. -/
def homologyRestrictionIso {F : Sheaf K AddCommGrpCat.{t}} (I : InjectiveResolution F) (p : ℕ) :
    Ψ.op ⋙ (pushforwardSections J K u I).homology p ≅
      (pushforwardSections J₀ K₀ (𝟭 C₀) (restrictedResolution K u K₀ Ψ I)).homology p :=
  (((pushforwardSections J K u I).sc p).mapHomologyIso
    ((Functor.whiskeringLeft C₀ᵒᵖ Dᵒᵖ AddCommGrpCat.{t}).obj Ψ.op)).symm

omit [HasSheafify J AddCommGrpCat.{t}] [HasSheafify J₀ AddCommGrpCat.{t}] in
/-- **Local vanishing transports along a cover-preserving functor.** If `Ψ : (C₀, J₀) ⥤ (D, J)`
preserves covers, and the sections over `U` of the homology presheaf of the section complex of
the restricted resolution die `J₀`-locally, then every section over `Ψ U` of the homology
presheaf of the restricted section complex of `I` dies `J`-locally. -/
theorem equalizerSieve_mem_of_restriction (hΨ : CoverPreserving J₀ J Ψ)
    {F : Sheaf K AddCommGrpCat.{t}} (I : InjectiveResolution F) (p : ℕ) (U : C₀)
    (hloc : ∀ y : ToType (((pushforwardSections J₀ K₀ (𝟭 C₀)
        (restrictedResolution K u K₀ Ψ I)).homology p).obj (op U)),
      Presheaf.equalizerSieve (X := op U) y 0 ∈ J₀ U)
    (x : ToType (((pushforwardSections J K u I).homology p).obj (op (Ψ.obj U)))) :
    Presheaf.equalizerSieve (X := op (Ψ.obj U)) x 0 ∈ J (Ψ.obj U) := by
  let e := homologyRestrictionIso J K u J₀ K₀ Ψ I p
  let y := (e.hom.app (op U)) x
  refine J.superset_covering ?_ (hΨ.cover_preserve (hloc y))
  rintro W f ⟨V, g, h, hg, rfl⟩
  show ((pushforwardSections J K u I).homology p).map (h ≫ Ψ.map g).op x =
    ((pushforwardSections J K u I).homology p).map (h ≫ Ψ.map g).op 0
  rw [map_zero, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have hg' : ((pushforwardSections J₀ K₀ (𝟭 C₀)
      (restrictedResolution K u K₀ Ψ I)).homology p).map g.op y = 0 := by
    simpa using hg
  have hx : ((pushforwardSections J K u I).homology p).map (Ψ.map g).op x = 0 := by
    have hnat := ConcreteCategory.congr_hom (e.hom.naturality g.op) x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
    simpa using congrArg (e.inv.app (op V)) (hnat.trans hg')
  rw [hx, map_zero]

end Transport

end Stacks.Cohomology.SectionComplexVanishing

end
