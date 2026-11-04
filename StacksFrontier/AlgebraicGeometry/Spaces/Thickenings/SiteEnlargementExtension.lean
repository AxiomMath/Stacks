module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementInverseImageRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafSquareZeroExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous

/-!
# Square-zero extensions after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` for `B` and let `f' : X' ⟶ Y'` be its inverse image on the enlarged
site. A square-zero extension `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` of the structure sheaf of `X` as an
`f⁻¹𝒪_Y`-algebra (`AlgebraicGeometry.Space.SquareZeroExtension`) transports to a square-zero
extension of the structure sheaf of `X'` as an `f'⁻¹𝒪_{Y'}`-algebra, whose restriction along the
transport of étale charts is the given one.

The transport is through the equivalences of categories given by restriction of sheaves along
the transport of étale charts, which is a dense subsite inclusion: sheaves of commutative rings
for `𝒜` and its structure maps, sheaves of modules for `ℐ` (the comparison lemma for modules,
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`), and sheaves of abelian groups for
the inclusion `ℐ ⟶ 𝒜`. The algebra structure is transported through the identification of
`f⁻¹𝒪_Y` with the restriction of `f'⁻¹𝒪_{Y'}`
(`AlgebraicGeometry.SiteEnlargement.inverseImageRingComparison`).

## Main definitions

* `AlgebraicGeometry.SiteEnlargement.transportExtension`: the transported square-zero extension.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.SiteEnlargement

/-- On any site, and for any universe of sections, the sheaf condition for presheaves of abelian
groups is preserved by the forgetful functor to sets: the forgetful functor is corepresentable,
by `ℤ`, hence preserves limits of every size. -/
theorem hasSheafCompose_forget_addCommGrpCat.{w, v, u'} {C : Type u'} [Category.{v} C]
    (J : GrothendieckTopology C) : J.HasSheafCompose (forget AddCommGrpCat.{w}) :=
  let : PreservesLimitsOfSize.{v, max u' v} (coyoneda.obj (op (AddCommGrpCat.of (ULift.{w} ℤ)))) :=
    ⟨inferInstance⟩
  let : PreservesLimitsOfSize.{v, max u' v} (forget AddCommGrpCat.{w}) :=
    preservesLimits_of_natIso AddCommGrpCat.coyonedaObjIsoForget
  hasSheafCompose_of_preservesLimitsOfSize J


open Space

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') {S : Scheme.{u}}
  {hS : B.Contains S} (hS' : B'.Contains S) {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  (E : SquareZeroExtension B S hS f)

/-- The transported extension sheaf: the sheaf of commutative rings on the small étale site of
`X'` whose restriction is the extension sheaf `𝒜`. -/
def transportA :
    Sheaf (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)
      CommRingCat.{u} :=
  (restrictRingSheaf h hS' X).asEquivalence.inverse.obj E.A

/-- The restriction of the transported extension sheaf is the extension sheaf. -/
def transportAIso : (restrictRingSheaf h hS' X).obj (transportA h hS' E) ≅ E.A :=
  (restrictRingSheaf h hS' X).asEquivalence.counitIso.app E.A

/-- The transported surjection onto the structure sheaf of `X'`. -/
def transportπ :
    transportA h hS' E ⟶
      (Space.smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).O :=
  (restrictRingSheaf h hS' X).preimage
    ((transportAIso h hS' E).hom ≫ E.π : (restrictRingSheaf h hS' X).obj (transportA h hS' E) ⟶
      (restrictRingSheaf h hS' X).obj
        (Space.smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).O)

/-- The restriction of the transported surjection is the given surjection `𝒜 ⟶ 𝒪_X`, read
through `transportAIso`. -/
theorem map_transportπ :
    (restrictRingSheaf h hS' X).map (transportπ h hS' E) = (transportAIso h hS' E).hom ≫ E.π :=
  (restrictRingSheaf h hS' X).map_preimage _

/-- The transported algebra structure. -/
def transportToBase :
    (inverseImageCommRingFunctor (Space.smallEtaleRingedToposHom B' S hS'
        ((changeBigSite B B' h S hS).map f)).toToposHom).obj
          (Space.smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj Y)).O ⟶
      transportA h hS' E :=
  (restrictRingSheaf h hS' X).preimage
    ((inverseImageRingComparison h hS' f).inv ≫ E.toBase ≫ (transportAIso h hS' E).inv)

/-- The restriction of the transported algebra structure is the given one, read through the
comparison `inverseImageRingComparison` and `transportAIso`. -/
theorem map_transportToBase :
    (restrictRingSheaf h hS' X).map (transportToBase h hS' E) =
      (inverseImageRingComparison h hS' f).inv ≫ E.toBase ≫ (transportAIso h hS' E).inv :=
  (restrictRingSheaf h hS' X).map_preimage _

/-- The transported surjection is a map of algebras over the inverse image of the structure sheaf
of `Y'`. -/
theorem transportToBase_π :
    transportToBase h hS' E ≫ transportπ h hS' E =
      (Space.smallEtaleRingedToposHom B' S hS'
        ((changeBigSite B B' h S hS).map f)).fSharpInverseImage := by
  apply (restrictRingSheaf h hS' X).map_injective
  refine ((restrictRingSheaf h hS' X).map_comp _ _).trans ?_
  rw [map_transportToBase, map_transportπ]
  refine (Category.assoc _ _ _).trans ((congrArg ((inverseImageRingComparison h hS' f).inv ≫ ·)
    ((Category.assoc _ _ _).trans (congrArg (E.toBase ≫ ·)
      (Iso.inv_hom_id_assoc (transportAIso h hS' E) E.π)))).trans ?_)
  refine (congrArg ((inverseImageRingComparison h hS' f).inv ≫ ·) E.toBase_π).trans ?_
  exact ((Iso.eq_inv_comp _).mpr (inverseImageRingComparison_fSharpInverseImage h hS' f)).symm

/-- **The transported surjection is a surjection of sheaves.** On underlying sheaves of sets it is
an epimorphism, because restriction along the transport of étale charts is an equivalence and the
restriction of the transported surjection is the given surjection up to an isomorphism. -/
theorem isLocallySurjective_transportπ : Sheaf.IsLocallySurjective (transportπ h hS' E) := by
  have hE : Epi ((sheafCompose (Space.SmallEtale.topology B S hS X.obj)
      (forget CommRingCat.{u})).map E.π) :=
    (Sheaf.isLocallySurjective_iff_epi _).mp
      ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).mp E.locallySurjective_π)
  have h1 : Epi ((sheafCompose (Space.SmallEtale.topology B S hS X.obj)
      (forget CommRingCat.{u})).map ((restrictRingSheaf h hS' X).map (transportπ h hS' E))) := by
    have e := (congrArg (sheafCompose (Space.SmallEtale.topology B S hS X.obj)
      (forget CommRingCat.{u})).map (map_transportπ h hS' E)).trans
        ((sheafCompose (Space.SmallEtale.topology B S hS X.obj) (forget CommRingCat.{u})).map_comp
          _ _)
    rw [e]
    have : IsIso ((sheafCompose (Space.SmallEtale.topology B S hS X.obj)
      (forget CommRingCat.{u})).map (transportAIso h hS' E).hom) := Functor.map_isIso _ _
    exact @epi_comp _ _ _ _ _ _ inferInstance _ hE
  have h3 : Epi ((sheafCompose (Space.SmallEtale.topology B' S hS'
      ((changeBigSite B B' h S hS).obj X).obj) (forget CommRingCat.{u})).map
        (transportπ h hS' E)) :=
    have : (restrictSheaf h hS' X).Faithful := (restrictSheafFullyFaithful h hS' X).faithful
    have : (restrictSheaf h hS' X).ReflectsEpimorphisms :=
      Functor.reflectsEpimorphisms_of_faithful _
    (restrictSheaf h hS' X).epi_of_epi_map h1
  exact (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    ((Sheaf.isLocallySurjective_iff_epi _).mpr h3)

section Kernel

/-- The structure sheaf of `X'`, as a sheaf of rings. -/
abbrev ringO' : Sheaf (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)
    RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf
    (Space.smallEtaleRingedSite B' S hS' ((changeBigSite B B' h S hS).obj X).obj
      ((changeBigSite B B' h S hS).obj X).property).O

/-- Restriction of sheaves of modules along the transport of étale charts is an equivalence. -/
def moduleTransportEquivalence :
    SheafOfModules.{u} (ringO' h hS' (X := X)) ≌ Space.Modules.{u, u} B S hS X.obj X.property :=
  haveI : (chartTransport B B' h S hS X).IsDenseSubsite (Space.SmallEtale.topology B S hS X.obj)
      (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj) :=
    chartTransport_isDenseSubsite B B' h S hS X
  Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (Space.SmallEtale.topology B S hS X.obj)
    (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)
    (chartTransport B B' h S hS X) (ringO' h hS' (X := X))

/-- The transported kernel. -/
def transportI : Space.Modules.{u, u} B' S hS' ((changeBigSite B B' h S hS).obj X).obj
    ((changeBigSite B B' h S hS).obj X).property :=
  (moduleTransportEquivalence h hS').inverse.obj E.I

/-- The restriction of the transported kernel is the kernel. -/
def transportIIso : (moduleTransportEquivalence h hS').functor.obj (transportI h hS' E) ≅ E.I :=
  (moduleTransportEquivalence h hS').counitIso.app E.I

/-- **The transported kernel is quasi-coherent**: quasi-coherence is intrinsic to the ringed topos,
in the form of its invariance under restriction along a special cocontinuous functor
(`Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff`). -/
theorem isQuasicoherentOnSite_transportI : (transportI h hS' E).IsQuasicoherentOnSite := by
  have : (chartTransport B B' h S hS X).IsDenseSubsite (Space.SmallEtale.topology B S hS X.obj)
      (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj) :=
    chartTransport_isDenseSubsite B B' h S hS X
  have : ∀ (U : Space.SmallEtale B S hS X.obj)
      (V : (Over ((chartTransport B B' h S hS X).obj U))ᵒᵖ),
      HasLimitsOfShape (StructuredArrow V (Over.post (X := U) (chartTransport B B' h S hS X)).op)
        AddCommGrpCat.{u} := fun _ _ => hasLimitsOfShape_of_essentiallySmall _ _
  exact (Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff
    (Space.SmallEtale.topology B S hS X.obj)
    (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)
    (chartTransport B B' h S hS X) (ringO' h hS' (X := X)) (transportI h hS' E)).mpr
    (SheafOfModules.IsQuasicoherentOnSite.of_iso (transportIIso h hS' E).symm E.quasicoherent)

end Kernel

section GlueTransported

variable (F' : Sheaf (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)
    (Type u))

/-- **Sections of a sheaf on the small étale site of `X'` glue from the transported charts**: a
family of sections over the transported charts mapping to `U'`, compatible with restriction along
morphisms of charts of `X`, is the family of restrictions of a section over `U'`. -/
theorem exists_section_of_transported
    {U' : Space.SmallEtale B' S hS' ((changeBigSite B B' h S hS).obj X).obj}
    (x : ∀ (U₃ : Space.SmallEtale B S hS X.obj), ((chartTransport B B' h S hS X).obj U₃ ⟶ U') →
      F'.obj.obj (op ((chartTransport B B' h S hS X).obj U₃)))
    (hx : ∀ (U₃ U₄ : Space.SmallEtale B S hS X.obj) (p : U₄ ⟶ U₃)
      (n : (chartTransport B B' h S hS X).obj U₃ ⟶ U'),
      F'.obj.map ((chartTransport B B' h S hS X).map p).op (x U₃ n) =
        x U₄ ((chartTransport B B' h S hS X).map p ≫ n)) :
    ∃ y : F'.obj.obj (op U'), ∀ (U₃ : Space.SmallEtale B S hS X.obj)
      (n : (chartTransport B B' h S hS X).obj U₃ ⟶ U'), F'.obj.map n.op y = x U₃ n := by
  have hF := (isSheaf_iff_isSheaf_of_type _ F'.obj).mp F'.property
  let fam : Presieve.FamilyOfElements F'.obj
      (Sieve.coverByImage (chartTransport B B' h S hS X) U').arrows :=
    fun _ _ hk => F'.obj.map hk.some.lift.op (x hk.some.obj hk.some.map)
  have hrestr : ∀ {W} (k : W ⟶ U') (hk : Sieve.coverByImage (chartTransport B B' h S hS X) U' k)
      (U₃ : Space.SmallEtale B S hS X.obj) (n : (chartTransport B B' h S hS X).obj U₃ ⟶ W),
      F'.obj.map n.op (fam k hk) = x U₃ (n ≫ k) := by
    intro W k hk U₃ n
    let p := (chartTransportFullyFaithful B B' h S hS X).preimage (n ≫ hk.some.lift)
    have hp : (chartTransport B B' h S hS X).map p = n ≫ hk.some.lift :=
      (chartTransportFullyFaithful B B' h S hS X).map_preimage _
    show F'.obj.map n.op (F'.obj.map hk.some.lift.op _) = _
    rw [← types_comp_apply (F'.obj.map hk.some.lift.op) (F'.obj.map n.op), ← F'.obj.map_comp,
      ← op_comp, ← hp, hx]
    exact congrArg (x U₃) (by rw [hp, Category.assoc, hk.some.fac])
  have hcompat : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    refine section_ext (F' := F') fun U₃ n => ?_
    rw [← types_comp_apply (F'.obj.map g₁.op) (F'.obj.map n.op), ← F'.obj.map_comp, ← op_comp,
      ← types_comp_apply (F'.obj.map g₂.op) (F'.obj.map n.op), ← F'.obj.map_comp, ← op_comp,
      hrestr, hrestr]
    exact congrArg (x U₃) (by rw [Category.assoc, Category.assoc, e])
  refine ⟨(hF _ ((chartTransport_isCoverDense B B' h S hS X).is_cover U')).amalgamate fam hcompat,
    fun U₃ n => ?_⟩
  have hv := Presieve.IsSheafFor.valid_glue
    (hF _ ((chartTransport_isCoverDense B B' h S hS X).is_cover U')) hcompat n
    (Presieve.in_coverByImage _ n)
  have e := hrestr n (Presieve.in_coverByImage _ n) U₃ (𝟙 _)
  exact hv.trans ((FunctorToTypes.map_id_apply F'.obj _).symm.trans
    (e.trans (congrArg (x U₃) (Category.id_comp n))))

end GlueTransported

section Inclusion

/-- The transported kernel, as a sheaf of sets. -/
abbrev transportISet :
    Sheaf (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj) (Type u) :=
  haveI := hasSheafCompose_forget_addCommGrpCat.{u}
    (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)
  (sheafCompose _ (forget AddCommGrpCat.{u})).obj
    ((SheafOfModules.toSheaf _).obj (transportI h hS' E))

/-- The transported extension sheaf, as a sheaf of sets. -/
abbrev transportASet :
    Sheaf (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj) (Type u) :=
  (sheafCompose _ (forget CommRingCat.{u})).obj (transportA h hS' E)

/-- The inclusion of the restricted transported kernel into the restricted transported extension
sheaf, through the given inclusion `ℐ ⟶ 𝒜`. -/
def restrictedInclusion :
    (restrictSheaf h hS' X).obj (transportISet h hS' E) ⟶
      (restrictSheaf h hS' X).obj (transportASet h hS' E) :=
  ⟨{ app := fun U => TypeCat.ofHom fun z =>
        (transportAIso h hS' E).inv.hom.app U (E.ι U ((transportIIso h hS' E).hom.val.app U z))
     naturality := fun U V g => by
       apply TypeCat.homEquiv.injective
       funext z
       change (transportAIso h hS' E).inv.hom.app V (E.ι V
          ((transportIIso h hS' E).hom.val.app V ((transportI h hS' E).val.map
            ((chartTransport B B' h S hS X).map g.unop).op z))) =
        (transportA h hS' E).val.map ((chartTransport B B' h S hS X).map g.unop).op
          ((transportAIso h hS' E).inv.hom.app U (E.ι U ((transportIIso h hS' E).hom.val.app U z)))
       have e1 := PresheafOfModules.naturality_apply (transportIIso h hS' E).hom.val g z
       have e2 := NatTrans.naturality_apply (transportAIso h hS' E).inv.hom g
         (E.ι U ((transportIIso h hS' E).hom.val.app U z))
       refine (congrArg (fun w => (transportAIso h hS' E).inv.hom.app V (E.ι V w)) e1).trans ?_
       refine (congrArg (fun w => (transportAIso h hS' E).inv.hom.app V w)
         (E.naturality g _)).trans ?_
       exact e2 }⟩

/-- The transported inclusion, as a morphism of sheaves of sets on the small étale site of
`X'`. -/
def transportInclusionSet : transportISet h hS' E ⟶ transportASet h hS' E :=
  (restrictSheaf h hS' X).preimage (restrictedInclusion h hS' E)

/-- On a transported chart, the transported inclusion is the given inclusion `ℐ ⟶ 𝒜`, read
through `transportIIso` and `transportAIso`. -/
theorem transportInclusionSet_app (U : Space.SmallEtale B S hS X.obj)
    (z : (transportI h hS' E).val.obj (op ((chartTransport B B' h S hS X).obj U))) :
    (transportInclusionSet h hS' E).hom.app (op ((chartTransport B B' h S hS X).obj U)) z =
      (transportAIso h hS' E).inv.hom.app (op U)
        (E.ι (op U) ((transportIIso h hS' E).hom.val.app (op U) z)) :=
  congrArg (fun m => m.hom.app (op U) z) ((restrictSheaf h hS' X).map_preimage
    (restrictedInclusion h hS' E))

end Inclusion

section Elementwise

variable (U₃ : Space.SmallEtale B S hS X.obj)

/-- `transportAIso` followed by its inverse is the identity, on sections over a chart of `X`. -/
theorem transportAIso_hom_inv_apply (a : E.A.val.obj (op U₃)) :
    (transportAIso h hS' E).hom.hom.app (op U₃)
      ((transportAIso h hS' E).inv.hom.app (op U₃) a) = a :=
  congrArg (fun m => m.hom.app (op U₃) a) (transportAIso h hS' E).inv_hom_id

/-- The inverse of `transportAIso` followed by `transportAIso` is the identity, on sections over a
transported chart. -/
theorem transportAIso_inv_hom_apply
    (w : (transportA h hS' E).val.obj (op ((chartTransport B B' h S hS X).obj U₃))) :
    (transportAIso h hS' E).inv.hom.app (op U₃)
      ((transportAIso h hS' E).hom.hom.app (op U₃) w) = w :=
  congrArg (fun m => m.hom.app (op U₃) w) (transportAIso h hS' E).hom_inv_id

/-- `transportIIso` followed by its inverse is the identity, on sections over a chart of `X`. -/
theorem transportIIso_hom_inv_apply (y : E.I.val.obj (op U₃)) :
    (transportIIso h hS' E).hom.val.app (op U₃)
      ((transportIIso h hS' E).inv.val.app (op U₃) y) = y :=
  congrArg (fun m => m.val.app (op U₃) y) (transportIIso h hS' E).inv_hom_id

/-- The inverse of `transportIIso` followed by `transportIIso` is the identity, on sections over a
transported chart. -/
theorem transportIIso_inv_hom_apply
    (z : (transportI h hS' E).val.obj (op ((chartTransport B B' h S hS X).obj U₃))) :
    (transportIIso h hS' E).inv.val.app (op U₃)
      ((transportIIso h hS' E).hom.val.app (op U₃) z) = z :=
  congrArg (fun m => m.val.app (op U₃) z) (transportIIso h hS' E).hom_inv_id

/-- The transported surjection on a transported chart. -/
theorem transportπ_app
    (w : (transportA h hS' E).val.obj (op ((chartTransport B B' h S hS X).obj U₃))) :
    (transportπ h hS' E).hom.app (op ((chartTransport B B' h S hS X).obj U₃)) w =
      E.π.hom.app (op U₃) ((transportAIso h hS' E).hom.hom.app (op U₃) w) :=
  congrArg (fun m => m.hom.app (op U₃) w) (map_transportπ h hS' E)

end Elementwise

section Axioms

/-- The kernel inclusion of a square-zero extension is injective on sections. -/
theorem SquareZeroExtension_ι_injective (U : (Space.SmallEtale B S hS X.obj)ᵒᵖ) :
    Function.Injective (E.ι U) := by
  intro y₁ y₂ e
  obtain ⟨z, -, hz⟩ := E.exact_kernel U (E.ι U y₂) (E.mem_kernel U y₂)
  exact (hz y₁ e).trans (hz y₂ rfl).symm

/-- The transported inclusion is injective on the transported charts. -/
theorem transportInclusionSet_injective (U₃ : Space.SmallEtale B S hS X.obj) :
    Function.Injective ((transportInclusionSet h hS' E).hom.app
      (op ((chartTransport B B' h S hS X).obj U₃))) := by
  intro z₁ z₂ e
  have e1 := ((transportInclusionSet_app h hS' E U₃ z₁).symm.trans e).trans
    (transportInclusionSet_app h hS' E U₃ z₂)
  have e2 := ((transportAIso_hom_inv_apply h hS' E U₃ _).symm.trans
    (congrArg ((transportAIso h hS' E).hom.hom.app (op U₃)) e1)).trans
    (transportAIso_hom_inv_apply h hS' E U₃ _)
  exact ((transportIIso_inv_hom_apply h hS' E U₃ z₁).symm.trans
    (congrArg ((transportIIso h hS' E).inv.val.app (op U₃))
      (SquareZeroExtension_ι_injective E (op U₃) e2))).trans
    (transportIIso_inv_hom_apply h hS' E U₃ z₂)

/-- The transported inclusion commutes with restriction. -/
theorem transportInclusionSet_naturality {V W : (Space.SmallEtale B' S hS'
      ((changeBigSite B B' h S hS).obj X).obj)ᵒᵖ} (g : V ⟶ W) (z : (transportI h hS' E).val.obj V) :
    (transportInclusionSet h hS' E).hom.app W ((transportI h hS' E).val.map g z) =
      (transportA h hS' E).val.map g ((transportInclusionSet h hS' E).hom.app V z) :=
  NatTrans.naturality_apply (transportInclusionSet h hS' E).hom g z

/-- The transported inclusion, as a homomorphism of abelian groups on sections. -/
def transportι (V : (Space.SmallEtale B' S hS' ((changeBigSite B B' h S hS).obj X).obj)ᵒᵖ) :
    (transportI h hS' E).val.obj V →+ (transportA h hS' E).val.obj V where
  toFun := (transportInclusionSet h hS' E).hom.app V
  map_zero' := by
    refine section_ext (F' := transportASet h hS' E) fun U₃ n => ?_
    change (transportA h hS' E).val.map n.op _ = (transportA h hS' E).val.map n.op 0
    refine (transportInclusionSet_naturality h hS' E n.op 0).symm.trans ?_
    refine (congrArg _ (map_zero ((transportI h hS' E).val.map n.op).hom)).trans ?_
    refine (transportInclusionSet_app h hS' E U₃ 0).trans ?_
    refine Eq.trans ?_ (map_zero ((transportA h hS' E).val.map n.op).hom).symm
    refine (congrArg (ConcreteCategory.hom ((transportAIso h hS' E).inv.hom.app (op U₃)))
      ((congrArg (E.ι (op U₃)) (map_zero (ConcreteCategory.hom
        ((transportIIso h hS' E).hom.val.app (op U₃))))).trans (map_zero (E.ι (op U₃))))).trans ?_
    exact map_zero _
  map_add' z₁ z₂ := by
    refine section_ext (F' := transportASet h hS' E) fun U₃ n => ?_
    change (transportA h hS' E).val.map n.op _ = (transportA h hS' E).val.map n.op (_ + _)
    refine (transportInclusionSet_naturality h hS' E n.op _).symm.trans ?_
    refine Eq.trans ?_ (map_add ((transportA h hS' E).val.map n.op).hom _ _).symm
    refine Eq.trans ?_ (congrArg₂ (· + ·) (transportInclusionSet_naturality h hS' E n.op z₁)
      (transportInclusionSet_naturality h hS' E n.op z₂))
    refine (congrArg _ (map_add ((transportI h hS' E).val.map n.op).hom z₁ z₂)).trans ?_
    refine (transportInclusionSet_app h hS' E U₃ _).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· + ·) (transportInclusionSet_app h hS' E U₃ _).symm
      (transportInclusionSet_app h hS' E U₃ _).symm)
    refine (congrArg (ConcreteCategory.hom ((transportAIso h hS' E).inv.hom.app (op U₃)))
      ((congrArg (E.ι (op U₃)) (map_add (ConcreteCategory.hom
        ((transportIIso h hS' E).hom.val.app (op U₃))) _ _)).trans
          (map_add (E.ι (op U₃)) _ _))).trans ?_
    exact map_add _ _ _

end Axioms

section Axioms2

/-- The structure sheaf of `X'`, as a sheaf of sets. -/
abbrev structureSet' :
    Sheaf (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj) (Type u) :=
  (sheafCompose _ (forget CommRingCat.{u})).obj
    (Space.smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).O

/-- The transported inclusion followed by the transported surjection, on a transported chart. -/
theorem transportπ_transportInclusionSet_app (U₃ : Space.SmallEtale B S hS X.obj)
    (z : (transportI h hS' E).val.obj (op ((chartTransport B B' h S hS X).obj U₃))) :
    (transportπ h hS' E).hom.app (op ((chartTransport B B' h S hS X).obj U₃))
      ((transportInclusionSet h hS' E).hom.app (op ((chartTransport B B' h S hS X).obj U₃)) z) =
        0 :=
  (congrArg _ (transportInclusionSet_app h hS' E U₃ z)).trans ((transportπ_app h hS' E U₃ _).trans
    ((congrArg (E.π.hom.app (op U₃)) (transportAIso_hom_inv_apply h hS' E U₃ _)).trans
      (E.mem_kernel _ _)))

/-- The transported inclusion lands in the kernel of the transported surjection. -/
theorem transport_mem_kernel
    (V : (Space.SmallEtale B' S hS' ((changeBigSite B B' h S hS).obj X).obj)ᵒᵖ)
    (z : (transportI h hS' E).val.obj V) :
    (transportπ h hS' E).hom.app V (transportι h hS' E V z) = 0 := by
  refine section_ext (F' := structureSet' h hS') fun U₃ n => ?_
  show (Space.smallEtaleRingedTopos B' S hS'
      ((changeBigSite B B' h S hS).obj X)).O.val.map n.op _ =
    (Space.smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).O.val.map n.op 0
  refine (NatTrans.naturality_apply (transportπ h hS' E).hom n.op _).symm.trans ?_
  refine (congrArg _ (transportInclusionSet_naturality h hS' E n.op z).symm).trans ?_
  refine (transportπ_transportInclusionSet_app h hS' E U₃ _).trans ?_
  exact (map_zero _).symm

/-- A transported-kernel section, restricted to a transported chart and included in the transported
extension sheaf, is the given inclusion applied to its restriction read through `transportIIso`. -/
private theorem map_transportι_eq
    {V : (Space.SmallEtale B' S hS' ((changeBigSite B B' h S hS).obj X).obj)ᵒᵖ}
    (U₃ : Space.SmallEtale B S hS X.obj) (n : (chartTransport B B' h S hS X).obj U₃ ⟶ V.unop)
    (z : (transportI h hS' E).val.obj V) :
    (transportA h hS' E).val.map n.op (transportι h hS' E V z) =
      (transportAIso h hS' E).inv.hom.app (op U₃) (E.ι (op U₃)
        ((transportIIso h hS' E).hom.val.app (op U₃) ((transportI h hS' E).val.map n.op z))) :=
  (transportInclusionSet_naturality h hS' E n.op z).symm.trans
    (transportInclusionSet_app h hS' E U₃ _)

/-- The product of two sections of the transported kernel vanishes in the transported extension
sheaf. -/
theorem transport_square_zero
    (V : (Space.SmallEtale B' S hS' ((changeBigSite B B' h S hS).obj X).obj)ᵒᵖ)
    (z₁ z₂ : (transportI h hS' E).val.obj V) :
    transportι h hS' E V z₁ * transportι h hS' E V z₂ = 0 := by
  refine section_ext (F' := transportASet h hS' E) fun U₃ n => ?_
  show (transportA h hS' E).val.map n.op (_ * _) = (transportA h hS' E).val.map n.op 0
  rw [map_mul, map_zero, map_transportι_eq, map_transportι_eq]
  exact (map_mul (ConcreteCategory.hom ((transportAIso h hS' E).inv.hom.app (op U₃)))
    _ _).symm.trans ((congrArg (ConcreteCategory.hom ((transportAIso h hS' E).inv.hom.app (op U₃)))
      (E.square_zero _ _ _)).trans (map_zero _))

end Axioms2

section Exact

/-- On a transported chart, every section killed by the transported surjection comes from the
transported kernel. -/
theorem exists_transportInclusionSet_eq (U₃ : Space.SmallEtale B S hS X.obj)
    (w : (transportA h hS' E).val.obj (op ((chartTransport B B' h S hS X).obj U₃)))
    (hw : (transportπ h hS' E).hom.app (op ((chartTransport B B' h S hS X).obj U₃)) w = 0) :
    ∃ z, (transportInclusionSet h hS' E).hom.app (op ((chartTransport B B' h S hS X).obj U₃)) z =
      w := by
  obtain ⟨y, hy, -⟩ := E.exact_kernel (op U₃) ((transportAIso h hS' E).hom.hom.app (op U₃) w)
    ((transportπ_app h hS' E U₃ w).symm.trans hw)
  refine ⟨(transportIIso h hS' E).inv.val.app (op U₃) y, ?_⟩
  refine (transportInclusionSet_app h hS' E U₃ _).trans ?_
  refine (congrArg (fun t => (transportAIso h hS' E).inv.hom.app (op U₃) (E.ι (op U₃) t))
    (transportIIso_hom_inv_apply h hS' E U₃ y)).trans ?_
  exact (congrArg ((transportAIso h hS' E).inv.hom.app (op U₃)) hy).trans
    (transportAIso_inv_hom_apply h hS' E U₃ w)

/-- A section of the transported extension sheaf killed by the transported surjection comes from a
unique section of the transported kernel. -/
theorem transport_exact_kernel
    (V : (Space.SmallEtale B' S hS' ((changeBigSite B B' h S hS).obj X).obj)ᵒᵖ)
    (a : (transportA h hS' E).val.obj V) (ha : (transportπ h hS' E).hom.app V a = 0) :
    ∃! z, transportι h hS' E V z = a := by
  have hloc : ∀ (U₃ : Space.SmallEtale B S hS X.obj)
      (n : (chartTransport B B' h S hS X).obj U₃ ⟶ V.unop),
      (transportπ h hS' E).hom.app (op ((chartTransport B B' h S hS X).obj U₃))
        ((transportA h hS' E).val.map n.op a) = 0 := fun U₃ n =>
    (NatTrans.naturality_apply (transportπ h hS' E).hom n.op a).trans
      ((congrArg _ ha).trans (map_zero _))
  let x : ∀ (U₃ : Space.SmallEtale B S hS X.obj),
      ((chartTransport B B' h S hS X).obj U₃ ⟶ V.unop) →
        (transportISet h hS' E).obj.obj (op ((chartTransport B B' h S hS X).obj U₃)) :=
    fun U₃ n => (exists_transportInclusionSet_eq h hS' E U₃ _ (hloc U₃ n)).choose
  have hxa : ∀ U₃ n, (transportInclusionSet h hS' E).hom.app
      (op ((chartTransport B B' h S hS X).obj U₃)) (x U₃ n) =
        (transportA h hS' E).val.map n.op a := fun U₃ n =>
    (exists_transportInclusionSet_eq h hS' E U₃ _ (hloc U₃ n)).choose_spec
  obtain ⟨y, hy⟩ := exists_section_of_transported h hS' (transportISet h hS' E) x (by
    intro U₃ U₄ p n
    apply transportInclusionSet_injective h hS' E U₄
    refine (transportInclusionSet_naturality h hS' E ((chartTransport B B' h S hS X).map p).op
      _).trans ?_
    refine (congrArg _ (hxa U₃ n)).trans ?_
    refine Eq.trans ?_ (hxa U₄ _).symm
    exact (FunctorToTypes.map_comp_apply (transportASet h hS' E).obj n.op
      ((chartTransport B B' h S hS X).map p).op a).symm)
  refine ⟨y, ?_, fun z hz => ?_⟩
  · refine section_ext (F' := transportASet h hS' E) fun U₃ n => ?_
    exact (transportInclusionSet_naturality h hS' E n.op y).symm.trans
      ((congrArg _ (hy U₃ n)).trans (hxa U₃ n))
  · refine section_ext (F' := transportISet h hS' E) fun U₃ n => ?_
    apply transportInclusionSet_injective h hS' E U₃
    exact ((transportInclusionSet_naturality h hS' E n.op z).trans (congrArg _ hz)).trans
      ((congrArg ((transportInclusionSet h hS' E).hom.app
        (op ((chartTransport B B' h S hS X).obj U₃))) (hy U₃ n)).trans (hxa U₃ n)).symm

end Exact

section SMul

/-- The comparison of the kernels is linear over the structure sheaf. -/
theorem transportIIso_smul (U₃ : Space.SmallEtale B S hS X.obj)
    (r : (Space.smallEtaleRingedTopos B S hS X).O.val.obj (op U₃))
    (z : (transportI h hS' E).val.obj (op ((chartTransport B B' h S hS X).obj U₃))) :
    (transportIIso h hS' E).hom.val.app (op U₃)
        ((((transportI h hS' E).val.obj
          (op ((chartTransport B B' h S hS X).obj U₃))).smul r).hom z) =
      ((E.I.val.obj (op U₃)).smul r).hom ((transportIIso h hS' E).hom.val.app (op U₃) z) :=
  ((transportIIso h hS' E).hom.val.app (op U₃)).hom.map_smul r z

/-- Restriction of the transported kernel is linear over the restriction of the structure sheaf. -/
theorem transportI_map_smul {V W : (Space.SmallEtale B' S hS'
      ((changeBigSite B B' h S hS).obj X).obj)ᵒᵖ} (g : V ⟶ W)
    (r : (Space.smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj X)).O.val.obj V)
    (z : (transportI h hS' E).val.obj V) :
    (transportI h hS' E).val.map g ((((transportI h hS' E).val.obj V).smul r).hom z) =
      (((transportI h hS' E).val.obj W).smul
        ((Space.smallEtaleRingedTopos B' S hS'
          ((changeBigSite B B' h S hS).obj X)).O.val.map g r)).hom
          ((transportI h hS' E).val.map g z) :=
  PresheafOfModules.map_smul (transportI h hS' E).val g r z

/-- The module structure of the transported kernel is multiplication in the transported extension
sheaf through the transported surjection: `ι (π a • z) = a * ι z`. -/
theorem transport_smul_lift
    (V : (Space.SmallEtale B' S hS' ((changeBigSite B B' h S hS).obj X).obj)ᵒᵖ)
    (a : (transportA h hS' E).val.obj V) (z : (transportI h hS' E).val.obj V) :
    transportι h hS' E V
        ((((transportI h hS' E).val.obj V).smul ((transportπ h hS' E).hom.app V a)).hom z) =
      a * transportι h hS' E V z := by
  refine section_ext (F' := transportASet h hS' E) fun U₃ n => ?_
  show (transportA h hS' E).val.map n.op _ = (transportA h hS' E).val.map n.op (_ * _)
  refine Eq.trans ?_ (map_mul ((transportA h hS' E).val.map n.op).hom _ _).symm
  refine (map_transportι_eq h hS' E U₃ n _).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (transportA h hS' E).val.map n.op a * t)
    (map_transportι_eq h hS' E U₃ n z).symm)
  refine (congrArg (fun w => (transportAIso h hS' E).inv.hom.app (op U₃)
    (E.ι (op U₃) ((transportIIso h hS' E).hom.val.app (op U₃) w)))
    ((transportI_map_smul h hS' E n.op _ z).trans
      (congrArg (fun r => (((transportI h hS' E).val.obj
        (op ((chartTransport B B' h S hS X).obj U₃))).smul r).hom
          ((transportI h hS' E).val.map n.op z))
        (NatTrans.naturality_apply (transportπ h hS' E).hom n.op a).symm))).trans ?_
  refine (congrArg (fun t => (transportAIso h hS' E).inv.hom.app (op U₃) (E.ι (op U₃) t))
    (transportIIso_smul h hS' E U₃ _ _)).trans ?_
  refine (congrArg (fun t => (transportAIso h hS' E).inv.hom.app (op U₃) t)
    ((congrArg (fun r => E.ι (op U₃) (((E.I.val.obj (op U₃)).smul r).hom
      ((transportIIso h hS' E).hom.val.app (op U₃) ((transportI h hS' E).val.map n.op z))))
      (transportπ_app h hS' E U₃ _)).trans (E.smul_lift (op U₃) _ _))).trans ?_
  exact (map_mul (ConcreteCategory.hom ((transportAIso h hS' E).inv.hom.app (op U₃))) _ _).trans
    (congrArg (· * _) (transportAIso_inv_hom_apply h hS' E U₃ _))

end SMul

/-- **The transported square-zero extension** of the structure sheaf of `X'`, as an algebra over
the inverse image of the structure sheaf of `Y'`: its restriction along the transport of étale
charts is the given square-zero extension. -/
def transportExtension :
    SquareZeroExtension B' S hS' ((changeBigSite B B' h S hS).map f) where
  A := transportA h hS' E
  π := transportπ h hS' E
  locallySurjective_π := isLocallySurjective_transportπ h hS' E
  toBase := transportToBase h hS' E
  toBase_π := transportToBase_π h hS' E
  I := transportI h hS' E
  quasicoherent := isQuasicoherentOnSite_transportI h hS' E
  ι := transportι h hS' E
  naturality g x := transportInclusionSet_naturality h hS' E g x
  mem_kernel := transport_mem_kernel h hS' E
  exact_kernel := transport_exact_kernel h hS' E
  smul_lift := transport_smul_lift h hS' E
  square_zero := transport_square_zero h hS' E

end AlgebraicGeometry.SiteEnlargement

end
