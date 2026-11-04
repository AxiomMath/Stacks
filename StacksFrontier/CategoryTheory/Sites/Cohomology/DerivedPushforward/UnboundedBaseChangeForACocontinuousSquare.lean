module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.UnboundedBaseChangeForAnExactLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# Unbounded base change over a cocontinuous square of sites, under the source's condition (6)

Let
```
  (Sh(C'), O_{C'}) --g'--> (Sh(C), O_C)
        |                      |
        f'                     f
        v                      v
  (Sh(D'), O_{D'}) --g-->  (Sh(D), O_D)
```
be the commutative square of ringed topoi of Stacks 0FN6: all four morphisms come from
cocontinuous functors `u : C ⥤ D`, `u' : C' ⥤ D'`, `v : D' ⥤ D`, `v' : C' ⥤ C` (Stacks 00XO),
so that `f_* = {}_su` and `f'_* = {}_su'`; `u' ⋙ v = v' ⋙ u`; `v` and `v'` are continuous as
well as cocontinuous, so that `g^{-1}` and `(g')^{-1}` are restriction (Stacks 00XR); the
comparison functors `{}^{u'}_{V'} I ⥤ {}^u_{v(V')} I` of the index categories of Section 00XF are
cofinal; `g^{-1} O_D = O_{D'}` and `(g')^{-1} O_C = O_{C'}`; and `g'_! : Ab(C') ⥤ Ab(C)` is
exact. The conclusion is `Rf'_* ∘ (g')^* = g^* ∘ Rf_*` on the unbounded derived categories.

`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/BaseChangeOverASquareOfSites.lean`
proves that conclusion at four unrelated universes, but with condition (6) read on sheaves of
*modules* — left exactness of `Stacks.SheafOfModules.lowerShriek` — because that is where it
applies Stacks 08BJ, and by Stacks 0798 the two lower shrieks differ. This file proves it with
the source's own condition (6), for four sites at one universe. It is the cocontinuous-column
counterpart of `UnboundedBaseChangeForAnExactLowerShriek.lean`, which does the same for the
continuous rows of Stacks 0FN7.

## Main results

All names below are in the namespace `Stacks.Cohomology`.

* `DerivedBaseChange.nonempty_inverseImage_comp_totalDerivedPushforwardOf_iso`: Stacks 0FN6,
  with condition (6) as the source states it.
* `CocontinuousForgetModule.corepRepresentation`: sections over an object of `D` of the direct
  image along a cocontinuous functor `u : C ⥤ D` are corepresented by the sheafification of the
  free abelian presheaf on `u.op ⋙ yoneda.obj V`, which is sectionwise torsion free.
* `CocontinuousForgetModule.abelianPushforwardUnit_isIso_at_underlying_kInjective`: Stacks 0D6J
  for the direct image along a cocontinuous functor — the underlying abelian complex of a
  K-injective complex of modules computes the derived direct image of abelian sheaves.
* `DerivedBaseChange.isIso_totalRightDerivedOfAdditiveUnit_at_inverseImage_of_cocontinuous`: the
  inverse image of a K-injective complex of `O_C`-modules computes `Rf'_*`.

## The argument

The source's proof opens by reducing to abelian sheaves through Stacks 0D6J, and that is what is
done here. Abstractly, the base change isomorphism needs exactly one thing beyond the underived
identity of Stacks 0FN3: that `(g')^* I` compute `Rf'_*` for every K-injective complex `I` of
`O_C`-modules — this is
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit`. The module-level substitution
gets it by making `(g')^*I` K-injective again; the source gets it, from the weaker abelian
condition (6), in three steps:

* `(g')^{-1}` of abelian sheaves preserves K-injectivity (Stacks 08BJ for the adjunction
  `g'_! ⊣ (g')^{-1}` of Stacks 00XR), so if `I_ab ⟶ J^•` is a K-injective resolution of the
  underlying abelian complex of `I` then `(g')^{-1}I_ab ⟶ (g')^{-1}J^•` is one as well;
* its direct image `f'_*(g')^{-1}(I_ab ⟶ J^•)` is `g^{-1}f_*(I_ab ⟶ J^•)` by the first
  conclusion of Stacks 0FN1, and `f_*(I_ab ⟶ J^•)` is a quasi-isomorphism by Stacks 0D6J for the
  cocontinuous `u`, which the exact `g^{-1}` preserves; so `(g')^{-1}I_ab` computes the abelian
  `Rf'_*`;
* the forgetful functor to abelian sheaves is exact and reflects isomorphisms, and carries `f'_*`
  to the degreewise direct image `{}_su'` of abelian sheaves — on the nose, by
  `Stacks.SheafOfModules.pushforwardCocontinuous_comp_toSheaf` — so a comparison of right derived
  functors of modules may be checked after it
  (`Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget`), where the other half
  of what is needed — the abelian comparison at the underlying complex of *any* K-injective
  complex of `O_{C'}`-modules — is again Stacks 0D6J for a cocontinuous functor.

## Implementation notes

*Stacks 0D6J for a cocontinuous functor.* The library's Stacks 0D6J is for a morphism of ringed
sites, whose direct image of abelian sheaves is restriction along a continuous functor; what the
square of this tag needs is the same statement for `{}_su`, the direct image along a cocontinuous
`u : C ⥤ D`, which is right Kan extension along `u.op`. The proof of
`quasiIso_cocontinuousPushforward_map_of_isKInjective` is the proof of
`Stacks.Cohomology.ForgetModule.quasiIso_abelianPushforward_map_of_isKInjective` with one
substitution: sections over `V : D` of `{}_su F` are no longer sections of `F` over a single
object of `C`, so the corepresenting sheaf is not the free abelian sheaf on a representable but
`corep`, the sheafification of `u.op ⋙ yoneda.obj V ⋙ AddCommGrpCat.free`. That it corepresents
is the composite of the sheafification adjunction, the adjunction `u^p ⊣ u_p` of right Kan
extension, and the corepresentation of evaluation of presheaves by a free abelian presheaf, each
of which is additive; and its sections over `W` are `ℤ[u(W) ⟶ V]`, free hence torsion free, which
is the hypothesis the argument of parts (1) and (2) of Stacks 0D6J consumes.

*One universe.* Stacks 0D6J is available in this library for a site whose objects, morphisms,
sheaf sections and module sections lie in a single universe, so all four sites here do. The
`HasSheafify` and `WEqualsLocallyBijective` hypotheses are then automatic; they are carried as
section variables only so that instance search finds them locally, as in the files above.

*Condition (6) is the only hypothesis beyond the square.* The existence of `g'_!` is not assumed:
for a continuous `v'` the adjunction `g'_! ⊣ (g')^{-1}` is `Functor.sheafAdjunctionContinuous`,
available from the `HasSheafify` instances alone, so left exactness of `v'.sheafPullback` is the
whole of condition (6) and no adjointness hypothesis accompanies it.

*An isomorphism, asserted through `Nonempty`.* A right derived functor is determined only up to
a canonical isomorphism, and the underived input Stacks 0FN3 is itself a `Nonempty` — the
sheaf-level comparison of Stacks 0FN1 is a base change of right Kan extensions and not an
equality — so the conclusion is the non-emptiness of the type of isomorphisms, as it is for
Stacks 0FN3 itself.

## References

* [Stacks Project, Tag 0FN6](https://stacks.math.columbia.edu/tag/0FN6)
* [Stacks Project, Tag 0FN1](https://stacks.math.columbia.edu/tag/0FN1)
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open ModuleSheafCohomology

namespace Stacks.Cohomology.CocontinuousForgetModule

universe ua va ub vb u

section Corepresentation

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : C ⥤ D)
  [w.IsCocontinuous J K]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{u}, w.op.HasPointwiseRightKanExtension G]
  [HasSheafify J AddCommGrpCat.{u}]

/-- **The sheaf corepresenting sections over `V` of the direct image along a cocontinuous
functor**: the sheafification of the free abelian presheaf on `w.op ⋙ yoneda.obj V`, whose
sections over `W` are the free abelian group on `w(W) ⟶ V`. -/
abbrev corep (V : D) : Sheaf J AddCommGrpCat.{u} :=
  (presheafToSheaf J AddCommGrpCat.{u}).obj (w.op ⋙ yoneda.obj V ⋙ AddCommGrpCat.free)

/-- Restriction of presheaves of abelian groups along a functor is additive, addition of
morphisms of presheaves being pointwise. -/
instance additive_whiskeringLeft_op :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj w.op |>.Additive where
  map_add := rfl

/-- **Morphisms out of `corep` are the sections over `V` of the direct image along `w`.** The
bijection is the composite of the sheafification adjunction, the adjunction between restriction
along `w.op` and right Kan extension along it — which is what the direct image of a cocontinuous
functor is — and the corepresentation of evaluation at `V` of a presheaf of abelian groups by the
free abelian presheaf on `yoneda.obj V`. Each of the three is additive. -/
def sectionsCorepEquiv (V : D) (F : Sheaf J AddCommGrpCat.{u}) :
    (corep J w V ⟶ F) ≃+
      ToType (((w.sheafPushforwardCocontinuous AddCommGrpCat.{u} J K).obj F).val.obj (op V)) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homAddEquiv
      (w.op ⋙ yoneda.obj V ⋙ AddCommGrpCat.free) F).trans
    (((w.op.ranAdjunction AddCommGrpCat.{u}).homAddEquiv
        (yoneda.obj V ⋙ AddCommGrpCat.free) F.val).trans
      (freeEvaluationHomAddEquiv V (w.op.ran.obj F.val)))

/-- **Sections over `V` of the direct image along a cocontinuous functor are corepresented by
`corep`**, naturally in the sheaf. -/
def corepRepresentation (V : D) :
    w.sheafPushforwardCocontinuous AddCommGrpCat.{u} J K ⋙
        (sheafSections K AddCommGrpCat.{u}).obj (op V) ≅
      preadditiveCoyoneda.obj (op (corep J w V)) := by
  refine (NatIso.ofComponents
    (fun F => (sectionsCorepEquiv J K w V F).toAddCommGrpIso) ?_).symm
  intro F G β
  ext element
  change (corep J w V ⟶ F) at element
  change freeEvaluationHomAddEquiv V (w.op.ran.obj G.val)
      ((w.op.ranAdjunction AddCommGrpCat.{u}).homEquiv _ _
        ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ G (element ≫ β))) =
    (((w.sheafPushforwardCocontinuous AddCommGrpCat.{u} J K).map β).hom.app (op V))
      (freeEvaluationHomAddEquiv V (w.op.ran.obj F.val)
        ((w.op.ranAdjunction AddCommGrpCat.{u}).homEquiv _ _
          ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ F element)))
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  rfl

end Corepresentation

section QuasiIso

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : C ⥤ D)
  [w.IsCocontinuous J K]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{u}, w.op.HasPointwiseRightKanExtension G]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  (O : Sheaf J RingCat.{u})

/-- **Degreewise direct image along a cocontinuous functor takes a K-injective resolution of the
underlying abelian complex of a K-injective complex of modules to a quasi-isomorphism.** This is
`Stacks.Cohomology.ForgetModule.quasiIso_abelianPushforward_map_of_isKInjective` for `{}_sw`:
quasi-isomorphy of a morphism of complexes of abelian sheaves is detected on the underlying
complexes of presheaves, hence object by object of the target site; sections over `V` of `{}_sw`
are corepresented by `corep`, which is sectionwise torsion free; so the corepresentable criterion
applies with the bijectivity statement of parts (1) and (2) of Tag 0D6J as its input. -/
theorem quasiIso_cocontinuousPushforward_map_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective]
    {Jc : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ} [Jc.IsKInjective]
    (q : ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ Jc)
    [QuasiIso q] :
    QuasiIso (((w.sheafPushforwardCocontinuous AddCommGrpCat.{u} J K).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
  apply SupportedComplexes.sheafQuasiIso_of_presheafQuasiIso K
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro t
  change QuasiIso (((w.sheafPushforwardCocontinuous AddCommGrpCat.{u} J K ⋙
    (sheafSections K AddCommGrpCat.{u}).obj t).mapHomologicalComplex (ComplexShape.up ℤ)).map q)
  refine DerivedLowerShriek.quasiIso_mapHomologicalComplex_of_corepresentable
    _ _ (corepRepresentation J K w t.unop).symm q (fun n => ?_)
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)).map
        (q⟦n⟧'))) := by
    apply Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ))
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    change QuasiIso ((CategoryTheory.shiftFunctor
      (CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) n).map q)
    infer_instance
  refine DerivedLowerShriek.bijective_postcomp_of_qh_bijective _
    (ForgetModule.qh_map_bijective_single_of_isKInjective J O _
      (fun V => isTorsionFree_sheafify J _ (fun W => by
        change Module.IsTorsionFree ℤ (FreeAbelianGroup (w.obj W.unop ⟶ t.unop))
        exact Module.Flat.isTorsionFree) V) I n)
    (CochainComplex.IsKInjective.Qh_map_bijective _ (Jc⟦n⟧))

end QuasiIso

section DerivedAbelian

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (w : C ⥤ D)
  [w.IsCocontinuous J K]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{u}, w.op.HasPointwiseRightKanExtension G]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]

/-- Degreewise direct image of complexes of abelian sheaves along a cocontinuous functor of
sites, followed by localization. -/
abbrev homotopyAbelianPushforward :
    HomotopyCategory (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{u}) :=
  (w.sheafPushforwardCocontinuous AddCommGrpCat.{u} J K).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **Stacks 07A5 for the direct image of abelian sheaves along a cocontinuous functor:**
degreewise direct image followed by localization has a right derived functor on the whole
unbounded derived category, abelian sheaves on a small site being Grothendieck abelian. -/
@[sga "4 XVII 5.4.1" "partial"]
instance abelianPushforward_hasRightDerivedFunctor :
    (homotopyAbelianPushforward J K w).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  DerivedLowerShriek.alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian _

/-- The unbounded total direct image `Rf_*` of abelian sheaves along a cocontinuous functor. -/
abbrev derivedAbelianPushforward :
    DerivedCategory (Sheaf J AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{u}) :=
  (homotopyAbelianPushforward J K w).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- The canonical comparison from degreewise to derived direct image of abelian sheaves along a
cocontinuous functor. -/
abbrev derivedAbelianPushforwardUnit :
    homotopyAbelianPushforward J K w ⟶
      DerivedCategory.Qh ⋙ derivedAbelianPushforward J K w :=
  (homotopyAbelianPushforward J K w).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ))

variable (O : Sheaf J RingCat.{u})

/-- **Stacks 0D6J for the direct image along a cocontinuous functor of sites**: the underlying
abelian complex of a K-injective complex of `O`-modules computes the derived direct image of
abelian sheaves, in the sense that the comparison from degreewise to derived direct image is
invertible there. -/
theorem abelianPushforwardUnit_isIso_at_underlying_kInjective
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    IsIso ((derivedAbelianPushforwardUnit J K w).app
      ((HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)).obj
        (((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
  ForgetModule.rightDerivedUnit_isIso_of_quasiIso_degreewise
    (w.sheafPushforwardCocontinuous AddCommGrpCat.{u} J K)
    (derivedAbelianPushforward J K w) (derivedAbelianPushforwardUnit J K w) _
    (quasiIso_cocontinuousPushforward_map_of_isKInjective J K w O I _)

end DerivedAbelian

end Stacks.Cohomology.CocontinuousForgetModule

namespace Stacks.Cohomology.DerivedBaseChange

open Stacks.SheafOfModules Stacks.Cohomology.CocontinuousForgetModule

universe ua va ub vb u

section Square

attribute [local instance] HasDerivedCategory.standard

variable {C' : Type u} [Category.{u} C'] {C : Type u} [Category.{u} C] {D' : Type u}
  [Category.{u} D'] {D : Type u} [Category.{u} D] (J' : GrothendieckTopology C')
  (J : GrothendieckTopology C) (K' : GrothendieckTopology D') (K : GrothendieckTopology D)
  (u' : C' ⥤ D') (u : C ⥤ D) (v' : C' ⥤ C) (v : D' ⥤ D) [u.IsCocontinuous J K]
  [u'.IsCocontinuous J' K'] [v.IsContinuous K' K] [v.IsCocontinuous K' K]
  [v'.IsContinuous J' J] [v'.IsCocontinuous J' J]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{u}, u'.op.HasPointwiseRightKanExtension G]
  [∀ G : Cᵒᵖ ⥤ RingCat.{u}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ RingCat.{u}, u'.op.HasPointwiseRightKanExtension G]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify J' AddCommGrpCat.{u}]
  [HasSheafify K AddCommGrpCat.{u}] [HasSheafify K' AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [K'.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Quasi-isomorphy transported along an isomorphism of functors into complexes: the image of a
morphism under one functor is the image under the other conjugated by the isomorphism. -/
private theorem quasiIso_map_of_natIso {A : Type ua} [Category.{va} A] {B : Type ub}
    [Category.{vb} B] [Abelian B] {X Y : A ⥤ CochainComplex B ℤ} (η : X ≅ Y) {M N : A}
    (φ : M ⟶ N) (hq : QuasiIso (Y.map φ)) : QuasiIso (X.map φ) := by
  have h : η.hom.app M ≫ Y.map φ ≫ η.inv.app N = X.map φ := by
    rw [← Category.assoc, ← η.hom.naturality φ, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  have := hq
  rw [← h]
  infer_instance

omit [∀ (G : Cᵒᵖ ⥤ RingCat), u.op.HasPointwiseRightKanExtension G]
  [∀ (G : C'ᵒᵖ ⥤ RingCat), u'.op.HasPointwiseRightKanExtension G]
  [J.WEqualsLocallyBijective AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [K.WEqualsLocallyBijective AddCommGrpCat] [K'.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The first conclusion of Stacks 0FN1 on complexes of abelian sheaves**:
`f'_* ∘ (g')^{-1} ≅ g^{-1} ∘ f_*`, where `f_*`, `f'_*` are the direct images along the
cocontinuous `u`, `u'` and `(g')^{-1}`, `g^{-1}` are restriction along the continuous `v'`, `v`.
Quasi-isomorphy of the image of a morphism of complexes under one composite is therefore
quasi-isomorphy of its image under the other. -/
private theorem quasiIso_inverseImage_cocontinuousPushforward_of_square
    {M N : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ} (φ : M ⟶ N) (hsq : u' ⋙ v = v' ⋙ u)
    (hfinal : ∀ V' : D',
      (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
        (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final)
    (hq : QuasiIso (((v.sheafPushforwardContinuous AddCommGrpCat.{u} K' K).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (((u.sheafPushforwardCocontinuous AddCommGrpCat.{u} J K).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ))) :
    QuasiIso (((u'.sheafPushforwardCocontinuous AddCommGrpCat.{u} J' K').mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (((v'.sheafPushforwardContinuous AddCommGrpCat.{u} J' J).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ)) := by
  open Functor in
  obtain ⟨e⟩ :=
    (nonempty_sheafPushforwardContinuousCompCocontinuousIso_and_leftAdjointCompPullbackIso_of_final
      AddCommGrpCat.{u} J' J K' K u' u v' v hsq hfinal).1
  have η : (v'.sheafPushforwardContinuous AddCommGrpCat.{u} J' J).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (u'.sheafPushforwardCocontinuous AddCommGrpCat.{u} J' K').mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (u.sheafPushforwardCocontinuous AddCommGrpCat.{u} J K).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (v.sheafPushforwardContinuous AddCommGrpCat.{u} K' K).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (u.sheafPushforwardCocontinuous AddCommGrpCat.{u} J K ⋙
          v.sheafPushforwardContinuous AddCommGrpCat.{u} K' K)) (ComplexShape.up ℤ)).symm
  exact quasiIso_map_of_natIso η φ hq

variable (OC : Sheaf J RingCat.{u})

include K v in
omit [∀ (G : Cᵒᵖ ⥤ RingCat), u.op.HasPointwiseRightKanExtension G]
  [∀ (G : C'ᵒᵖ ⥤ RingCat), u'.op.HasPointwiseRightKanExtension G]
  [J'.WEqualsLocallyBijective AddCommGrpCat] [K.WEqualsLocallyBijective AddCommGrpCat]
  [K'.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The inverse image of the underlying abelian complex of a K-injective complex of modules
computes `Rf'_*` on abelian sheaves.** This is the source's proof of Stacks 0FN6 read on abelian
sheaves: choose a K-injective resolution `I_ab ⟶ J^•` on `C`; condition (6) and Stacks 08BJ make
`(g')^{-1}J^•` K-injective, so it is a K-injective resolution of `(g')^{-1}I_ab`; its direct
image `f'_*(g')^{-1}J^•` is `g^{-1}f_*J^•` by Stacks 0FN1, and `f_*(I_ab ⟶ J^•)` is a
quasi-isomorphism by Stacks 0D6J for the cocontinuous `u`, which `g^{-1}` preserves, being
exact. -/
theorem isIso_derivedCocontinuousPushforwardUnit_at_inverseImage
    [PreservesFiniteLimits (v'.sheafPullback AddCommGrpCat.{u} J' J)]
    (hsq : u' ⋙ v = v' ⋙ u)
    (hfinal : ∀ V' : D',
      (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
        (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final)
    (I : CochainComplex (SheafOfModules.{u} OC) ℤ) [I.IsKInjective] :
    IsIso ((derivedAbelianPushforwardUnit J' K' u').app
      ((HomotopyCategory.quotient (Sheaf J' AddCommGrpCat.{u}) (ComplexShape.up ℤ)).obj
        (((v'.sheafPushforwardContinuous AddCommGrpCat.{u} J' J).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((SheafOfModules.toSheaf OC).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) := by
  set Iab : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ :=
    ((SheafOfModules.toSheaf OC).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  set qI := (Stacks.Injectives.kInjectiveResolutionInclusion (Sheaf J AddCommGrpCat.{u})).app Iab
  have := isKInjective_mapHomologicalComplex_sheafPushforwardContinuous J' J v'
    ((Stacks.Injectives.kInjectiveResolutionFunctor (Sheaf J AddCommGrpCat.{u})).obj Iab)
  have hv'q : QuasiIso (((v'.sheafPushforwardContinuous AddCommGrpCat.{u} J'
      J).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology qI _
  have huq : QuasiIso (((u.sheafPushforwardCocontinuous AddCommGrpCat.{u} J
      K).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) :=
    quasiIso_cocontinuousPushforward_map_of_isKInjective J K u OC I qI
  have hvuq : QuasiIso (((v.sheafPushforwardContinuous AddCommGrpCat.{u} K'
      K).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((u.sheafPushforwardCocontinuous AddCommGrpCat.{u} J K).mapHomologicalComplex
          (ComplexShape.up ℤ)).map qI)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  exact ForgetModule.rightDerivedUnit_isIso_of_quasiIso_resolution_degreewise _ _ _
    (((v'.sheafPushforwardContinuous AddCommGrpCat.{u} J' J).mapHomologicalComplex
      (ComplexShape.up ℤ)).map qI)
    (quasiIso_inverseImage_cocontinuousPushforward_of_square J' J K' K u' u v' v qI hsq hfinal
      hvuq)

variable (OD : Sheaf K RingCat.{u})
  (f'Sharp : inverseImageRing K' K v OD ⟶
    (u'.sheafPushforwardCocontinuous RingCat.{u} J' K').obj (inverseImageRing J' J v' OC))

include K in
omit [∀ (G : Cᵒᵖ ⥤ RingCat), u.op.HasPointwiseRightKanExtension G]
  [K.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The inverse image of a K-injective complex of `O_C`-modules computes `Rf'_*`.** The
module-level statement that Stacks 0FN6 needs, and the one the source reaches through Stacks
0D6J: the forgetful functor to abelian sheaves is exact and reflects isomorphisms, it carries
`f'_*` to the degreewise direct image `{}_su'` of abelian sheaves, and the abelian comparison is
invertible both at the underlying complex of any K-injective complex of `O_{C'}`-modules — which
is Stacks 0D6J for the cocontinuous `u'` — and at this one, which is
`isIso_derivedCocontinuousPushforwardUnit_at_inverseImage`. -/
theorem isIso_totalRightDerivedOfAdditiveUnit_at_inverseImage_of_cocontinuous
    [PreservesFiniteLimits (v'.sheafPullback AddCommGrpCat.{u} J' J)]
    (hsq : u' ⋙ v = v' ⋙ u)
    (hfinal : ∀ V' : D',
      (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
        (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final)
    (I : CochainComplex (SheafOfModules.{u} OC) ℤ) (hI : I.IsKInjective) :
    IsIso ((UnboundedComplexes.totalRightDerivedOfAdditiveUnit
        (pushforwardCocontinuous.{u} u' f'Sharp)).app
      (((inverseImage.{u} J' J v' OC).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} OC) (ComplexShape.up ℤ)).obj I))) := by
  have := hI
  exact UnboundedComplexes.isIso_rightDerivedUnit_of_forget
    (pushforwardCocontinuous.{u} u' f'Sharp)
    (u'.sheafPushforwardCocontinuous AddCommGrpCat.{u} J' K')
    (_root_.SheafOfModules.toSheaf (inverseImageRing J' J v' OC))
    (_root_.SheafOfModules.toSheaf (inverseImageRing K' K v OD)) (Iso.refl _) _
    (derivedAbelianPushforward J' K' u') _
    (derivedAbelianPushforwardUnit J' K' u')
    (fun I' hI' => have := hI'
      abelianPushforwardUnit_isIso_at_underlying_kInjective J' K' u'
        (inverseImageRing J' J v' OC) I')
    _ (isIso_derivedCocontinuousPushforwardUnit_at_inverseImage J' J K' K u' u v' v OC hsq hfinal
        I)

include K in
/-- **Stacks 0FN6.** For a commutative square of ringed topoi whose four functors `u : C ⥤ D`,
`u' : C' ⥤ D'`, `v : D' ⥤ D`, `v' : C' ⥤ C` are cocontinuous — giving `f`, `f'`, `g`, `g'` with
`f_* = {}_su`, `f'_* = {}_su'` — with `u' ⋙ v = v' ⋙ u`, with `v` and `v'` continuous as well as
cocontinuous so that `g^{-1}`, `(g')^{-1}` are restriction, with the comparison functors
`{}^{u'}_{V'} I ⥤ {}^u_{v(V')} I` of the index categories of Section 00XF all cofinal, with
`g^{-1} O_D = O_{D'}` and `(g')^{-1} O_C = O_{C'}`, and with `g'_! : Ab(C') ⥤ Ab(C)` exact, we
have `Rf'_* ∘ (g')^* = g^* ∘ Rf_*` as functors `D(O_C) ⥤ D(O_{D'})`.

Condition (5) is built into the statement by taking the restrictions along `v` and `v'` as *the*
sheaves of rings on `D'` and `C'`, so that `g^* = g^{-1}` and `(g')^* = (g')^{-1}` are
`Stacks.SheafOfModules.inverseImage` and are exact; `(f')^♯` is the structure map the square
forces, as in Stacks 0FN3. Condition (6) is the hypothesis
`PreservesFiniteLimits (v'.sheafPullback AddCommGrpCat J' J)`: `v'.sheafPullback` is the left
adjoint `g'_! = (v')_s` of the inverse image `(g')^{-1} = (v')^p` of abelian sheaves, which
Stacks 00XR produces for a continuous and cocontinuous `v'`, and right exactness of a left
adjoint is automatic, so left exactness is the whole of the condition.

Both `Rf_*` and `Rf'_*` are the total right derived functors of the degreewise direct images of
sheaves of modules; nothing about them is assumed. The source's proof is followed exactly: the
underived identity is Stacks 0FN3, which is what the cofinality hypothesis `hfinal` — condition
(4) — feeds; condition (6) and Stacks 08BJ make `(g')^{-1}` preserve K-injectivity *of abelian
sheaves*, Stacks 0FN1 gives the underived identity there, and Stacks 0D6J carries the resulting
statement — that the inverse image of a K-injective complex of `O_C`-modules computes `Rf'_*` —
back to modules. -/
@[stacks 0FN6 "`Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*` on the unbounded derived categories
  `D(O_C) → D(O_{D'})`, for a commutative square of ringed topoi whose four functors `u`, `u'`,
  `v`, `v'` are cocontinuous, with `u' ⋙ v = v' ⋙ u`, with `v`, `v'` continuous as well, with
  the comparison functors `{}^{u'}_{V'} I → {}^u_{v(V')} I` of the index categories of Section
  00XF cofinal, with `g^{-1} O_D = O_{D'}` and `(g')^{-1} O_C = O_{C'}`, and with the tag's
  condition (6) in the source's own form: exactness of `g'_! : Ab(C') → Ab(C)`, written
  `PreservesFiniteLimits (v'.sheafPullback AddCommGrpCat J' J)`, right exactness of a left
  adjoint being automatic. `Rf_*` and `Rf'_*` are *constructed*, as the total right derived
  functors of the degreewise direct images of sheaves of modules, and nothing about them is
  required. The price of the source's condition (6) is that the four sites lie in one universe,
  which is where Stacks 0D6J, the transport from abelian sheaves to modules that the source's
  proof opens with, is available. An isomorphism rather than an equality, and asserted through
  `Nonempty` as its underived input Stacks 0FN3 is, a right derived functor being determined only
  up to a canonical isomorphism and the sheaf-level comparison of Stacks 0FN1 being a base change
  of right Kan extensions."]
theorem nonempty_inverseImage_comp_totalDerivedPushforwardOf_iso
    [PreservesFiniteLimits (v'.sheafPullback AddCommGrpCat.{u} J' J)]
    (fSharp : OD ⟶ (u.sheafPushforwardCocontinuous RingCat.{u} J K).obj OC)
    (hsq : u' ⋙ v = v' ⋙ u)
    (hcomm : f'Sharp = structureMapSquare (J' := J') (K' := K') fSharp hsq)
    (hfinal : ∀ V' : D',
      (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
        (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final) :
    Nonempty ((inverseImage.{u} J' J v' OC).mapDerivedCategory ⋙
        UnboundedComplexes.totalRightDerivedOfAdditive
          (pushforwardCocontinuous.{u} u' f'Sharp) ≅
      UnboundedComplexes.totalRightDerivedOfAdditive (pushforwardCocontinuous.{u} u fSharp) ⋙
        (inverseImage.{u} K' K v OD).mapDerivedCategory) := by
  subst hcomm
  obtain ⟨e⟩ := nonempty_inverseImage_comp_cocontinuousPushforwardOf_iso.{u} J' J K' K u' u v' v
    OC OD fSharp hsq hfinal
  exact ⟨UnboundedComplexes.derivedBaseChangeIsoOfUnit (inverseImage.{u} J' J v' OC)
    (inverseImage.{u} K' K v OD) (pushforwardCocontinuous.{u} u fSharp)
    (pushforwardCocontinuous.{u} u' (structureMapSquare (J' := J') (K' := K') fSharp hsq))
    (UnboundedComplexes.totalRightDerivedOfAdditive (pushforwardCocontinuous.{u} u fSharp))
    (UnboundedComplexes.totalRightDerivedOfAdditive
      (pushforwardCocontinuous.{u} u' (structureMapSquare (J' := J') (K' := K') fSharp hsq)))
    (UnboundedComplexes.totalRightDerivedOfAdditiveUnit
      (pushforwardCocontinuous.{u} u fSharp))
    (UnboundedComplexes.totalRightDerivedOfAdditiveUnit
      (pushforwardCocontinuous.{u} u' (structureMapSquare (J' := J') (K' := K') fSharp hsq)))
    e
    fun I hI => isIso_totalRightDerivedOfAdditiveUnit_at_inverseImage_of_cocontinuous J' J K' K
      u' u v' v OC OD (structureMapSquare (J' := J') (K' := K') fSharp hsq) hsq hfinal I hI⟩

end Square

end Stacks.Cohomology.DerivedBaseChange

end
