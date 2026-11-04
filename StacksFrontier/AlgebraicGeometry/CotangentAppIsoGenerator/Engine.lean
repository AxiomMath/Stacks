module

public import StacksFrontier.AlgebraicGeometry.CotangentAppIsoGenerator.PullbackTop
public import StacksFrontier.AlgebraicGeometry.CotangentAppIso.Sections
public import StacksFrontier.AlgebraicGeometry.ConormalUnitTransport.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.LocalityGenerator

/-!
# The generator formula for the part (2) engine of [Stacks, Tag 01R3]

`StacksFrontier.AlgebraicGeometry.CotangentAppIso.Sections` builds the part (2) engine of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3) —
`Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` and its conclusion
`affineSectionsIsoCotangent`, the `Γ(B, V)`-module isomorphism `Γ(j _* M, V) ≅ I.Cotangent` — and
its "What is not done" section records that the engine carries **no formula on ideal generators**,
so that it inhabits the *type* of the part (2) assertion of 01R3 without discharging it. Four
module docstrings in this cluster name that formula as the missing ingredient, and two of them give
a reason rather than a caution:

* `ConormalAffineShape.PullbackIso` records that the sections of
  `Stacks.Conormal.AffineShape.pullbackIsoPushforwardInv` cannot be computed because
  `CategoryTheory.Equivalence.mk` replaces the unit it is handed by
  `CategoryTheory.Equivalence.adjointifyη`;
* `LeibnizDerivation.Affine` records that of the five factors of
  `Stacks.Conormal.AffineShape.conormalSheafRestrictIsoAffineModel` "*not one of the five has an
  elementwise formula*, so a section cannot be carried across it".

Both are now false. `StacksFrontier.AlgebraicGeometry.CotangentAppIsoGenerator.PullbackTop`
refutes the first; this file assembles the elementwise chain and proves the formula.

## Main results

* `Stacks.Conormal.CotangentAppIsoGenerator.restrictAffineModelIso_val_app_top`: **the generator
  formula for the sheaf-level engine.** Over the top open the engine carries the section that the
  locality comparison `c` sends to the unit generator attached to a section `y` of the ideal sheaf
  of `j ∣_ V` to the unit generator attached to the matching section `x` of the affine model's
  ideal sheaf. The locality comparison enters with a *characterization* — the hypothesis `hc` —
  which is the one further argument the engine's own docstring says it needs, and it is exactly
  the shape `Stacks.Conormal.Locality.conormalSheafRestrictIso_unit_app` has.
* `Stacks.Conormal.CotangentAppIsoGenerator.affineSectionsIsoCotangent_apply`: **the generator
  formula for the part (2) identification itself.** With the same data, the isomorphism
  `Stacks.Conormal.CotangentAppIso.affineSectionsIsoCotangent` carries a section `s` of `j _* M`
  over `V` to `I.toCotangent a`, where `a ∈ I` names the section of the affine model's ideal
  sheaf matching `s`. This is the statement that
  `StacksFrontier.AlgebraicGeometry.DiagonalQuotientPresentation.Basic` and
  `StacksFrontier.AlgebraicGeometry.DiagonalCotangentTransport.Basic` both name as the remaining
  missing ingredient for [Stacks, Tag 08S2].
* `Stacks.Conormal.CotangentAppIsoGenerator.junction_val_app_top`: the source-slot junction
  `idealSheafIsoAffineModelOfMorphismRestrict` on global sections, obtained from
  `idealSheafIsoPullbackOfSquare_unit` and the injectivity of the inclusion of an ideal sheaf.
* The reading lemmas `trans_val_app`, `pushforward_mapIso_val_app_top`,
  `pushforwardComp_val_app`, `pushforwardComp_inv_val_app`, `pushforwardCongr_val_app_top`,
  `pullbackObjCongr_val_app_top`, `pullback_mapIso_unit_val_app_top`, `trans_apply` and
  `evaluation_mapIso_apply`: the factor-by-factor
  elementwise descriptions the assembly is made of.

## Route, and the four tooling facts it rests on

The engine is a five-fold composite whose middle factor is itself a six-fold composite, and every
factor now has an elementwise description:

1. `Stacks.Conormal.Restriction.restrictPushforwardIso_hom_app` — a presheaf restriction map; it
   is left abstract and appears inside the hypothesis `hc`.
2. the locality comparison — the hypothesis `hc`.
3. the junction, by `junction_val_app_top`, after
   `Stacks.Conormal.Locality.unit_naturality_app` has moved it inside the unit.
4. `Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackCompIso_app` and its inverse form,
   from `CotangentAppIsoGenerator.PullbackTop`.
5. `pullbackObjCongr_val_app_top`, by `subst`.
6. `Stacks.Conormal.AffineShape.pullbackIsoPushforwardInv_hom_app_top`, from
   `CotangentAppIsoGenerator.PullbackTop`.
7. the two `AlgebraicGeometry.Scheme.Modules.pushforwardComp` steps and the
   `pushforwardCongr` step, which over the top open are the identity on sections.

Four facts about *how* the assembly has to be written:

* **`f ⁻¹ᵁ ⊤ = ⊤` must be taken by `rfl` at the point where a direct image is read on sections**,
  which is why `pushforward_mapIso_val_app_top` is stated at `⊤` rather than at a general open:
  with a general open the chain's subsequent factors are read over `(j ∣_ V) ⁻¹ᵁ ⊤`, and every
  later lemma then fails to match a goal that is definitionally the one it describes.
* **The composite must be peeled by `refine Eq.trans (trans_val_app _ _ _ _) ?_`, not by `rw` or
  by `simp only` on the definition.** Unfolding `restrictAffineModelIso` and rewriting with the
  component lemmas leaves a goal that is not type-correct at implicit transparency — the error
  names `𝟙` at one display of a module against another display of the same module — and this is
  the same wall `ConormalAffineShape.PullbackIso` hit.
* **`rw` cannot be used for the inner factors at all.** With the composite peeled, the goal has
  seven nested `ModuleCat.Hom.hom` applications, and `rw` with any of the factor lemmas either
  exceeds the heartbeat budget inside `isDefEq` or reports "did not find an occurrence" on a
  pattern that is present. The factors are wrapped around the equation one at a time by
  `congrArg` instead.
* **`congrArg` with the function left as `_` makes no progress**: higher-order unification
  solves the metavariable by the identity, so the "wrapped" equation is the original one. The
  call sites therefore pass the function to `congrArg` directly, as a `fun` reading one factor
  on sections, so that it is matched first-order.

## Universe situation

A single universe `u`, as in the statements of 01R3 and 08S2.

## What is not done, and what the next step is

* **No clause of [Stacks, Tag 01R3] or [Stacks, Tag 08S2] is discharged and no `stacks`
  attribute is attached.** The part (2) assertion of 01R3 is the projection of a subtype whose
  second component is the generator formula *for every closed-immersion factorization and every
  open of it*; `affineSectionsIsoCotangent_apply` is that formula at one locality comparison,
  taken as a hypothesis, so the quantifier over factorizations is still not reduced — nothing
  here says two factorizations give the same answer.
* **The hypothesis `hc` is not discharged at either of the two shapes of the 01R3 statement.** For
  `Stacks.Conormal.CotangentAppIso.pushforwardConormalSectionsIsoCotangent` the comparison fed in
  is `Stacks.Conormal.Locality.conormalSheafRestrictIso`, whose generator formula
  `Stacks.Conormal.Locality.conormalSheafRestrictIso_unit_app` is proved and has exactly this
  shape — except that it is stated over the open `(i' ⁻¹ᵁ O).ι ⁻¹ᵁ (i' ⁻¹ᵁ O)`, which is `⊤` but
  not definitionally, so a transport along
  `Stacks.Conormal.Locality.preimage_ι_preimage_eq` is still owed. For
  `conormalAffineSectionsIsoCotangent` the comparison is
  `Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe`, which is
  `conormalSheafRestrictIso` followed by
  `Stacks.Conormal.AffineCotangent.Transport.idealSheafPullbackIsoOfIsoTarget`, and that further
  factor has no elementwise description yet.
* **Nothing about the module-structure comparison [Stacks, Tag 08S2] needs downstream**: the
  isomorphism here is `Γ(B, V)`-linear, and `Stacks.LeibnizDerivation.kaehlerToConormal` lives in
  `ModuleCat Γ(X, U)`; `Stacks.LeibnizDerivation.surjective_diagRes_appTop` is what makes that
  step free, and it is not taken here.
* **Nothing about the square of the ideal or epimorphy of the quotient map.**

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal.CotangentAppIsoGenerator

/-! ### Reading a composite of isomorphisms of modules on sections -/

/-- A composite of isomorphisms of sheaves of modules, read on sections over an open: the two
factors applied in turn. This holds by `rfl` and is stated so that the chain of factors of
`Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` can be peeled off one at a time by
`rw`, rather than by unfolding the whole composite at once. -/
theorem trans_val_app {X : Scheme.{u}} {P Q R : X.Modules} (p : P ≅ Q) (q : Q ≅ R)
    (W : X.Opens) (x : Γ(P, W)) :
    ((p ≪≫ q).hom.val.app (.op W)).hom x =
      ((q.hom.val.app (.op W)).hom ((p.hom.val.app (.op W)).hom x)) :=
  rfl

/-- A direct image of an isomorphism of modules, read on sections: the isomorphism read on
sections over the preimage open. -/
theorem pushforward_mapIso_val_app_top {X Y : Scheme.{u}} (f : X ⟶ Y) {P Q : X.Modules}
    (g : P ≅ Q) (s : Γ((Scheme.Modules.pushforward f).obj P, (⊤ : Y.Opens))) :
    (((Scheme.Modules.pushforward f).mapIso g).hom.val.app (.op ⊤)).hom s =
      (g.hom.val.app (.op (⊤ : X.Opens))).hom s :=
  rfl

/-- Naturality of the unit of `g^* ⊣ g _*` over the top open, at an isomorphism of modules
presented as `CategoryTheory.Functor.mapIso`: the inverse image of the isomorphism carries the
unit generator attached to `t` to the unit generator attached to the image of `t`. This is
`Stacks.Conormal.Locality.unit_naturality_app` in the spelling the chain produces. -/
theorem pullback_mapIso_unit_val_app_top {A B : Scheme.{u}} (g : A ⟶ B) {P Q : B.Modules}
    (ψ : P ≅ Q) (t : Γ(P, (⊤ : B.Opens))) :
    ((((Scheme.Modules.pullback g).mapIso ψ).hom.val.app (.op (⊤ : A.Opens))).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app P).val.app (.op ⊤)).hom t)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app Q).val.app (.op ⊤)).hom
        ((ψ.hom.val.app (.op ⊤)).hom t) :=
  Locality.unit_naturality_app g ψ.hom ⊤ t

/-- `AlgebraicGeometry.Scheme.Modules.pushforwardComp` is the identity on sections, in the
`val.app` spelling. -/
theorem pushforwardComp_val_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : X.Modules)
    (W : Z.Opens) (s : Γ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).obj N, W)) :
    (((Scheme.Modules.pushforwardComp f g).hom.app N).val.app (.op W)).hom s = s := by
  have h : ((Scheme.Modules.pushforwardComp f g).hom.app N).app W s = s := by simp; rfl
  exact h

/-- `AlgebraicGeometry.Scheme.Modules.pushforwardComp` inverted is the identity on sections. -/
theorem pushforwardComp_inv_val_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : X.Modules)
    (W : Z.Opens) (s : Γ((Scheme.Modules.pushforward (f ≫ g)).obj N, W)) :
    (((Scheme.Modules.pushforwardComp f g).inv.app N).val.app (.op W)).hom s = s := by
  have h : ((Scheme.Modules.pushforwardComp f g).inv.app N).app W s = s := by simp; rfl
  exact h

/-- `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` is the identity on sections over the top
open: it is a presheaf restriction map along `f ⁻¹ᵁ ⊤ = g ⁻¹ᵁ ⊤`, whose two sides are both `⊤`. -/
theorem pushforwardCongr_val_app_top {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g)
    (N : X.Modules) (s : Γ((Scheme.Modules.pushforward f).obj N, (⊤ : Y.Opens))) :
    (((Scheme.Modules.pushforwardCongr hf).hom.app N).val.app (.op ⊤)).hom s = s := by
  have h : ((Scheme.Modules.pushforwardCongr hf).hom.app N).app ⊤ s = s := by
    simp only [Scheme.Modules.pushforwardCongr_hom_app_app]
    exact AffineShape.map_eqToHom_self N _ s
  exact h

/-- Transporting the module pullback along an equality of morphisms carries the unit generator
over the top open to the unit generator for the other morphism.

Discharged by `subst`, after which the transport is the identity. This is the elementwise form
of `Stacks.Conormal.AffineShape.unit_comp_map_pullbackObjCongr`, which it does not use: over the
top open the correcting `pushforwardCongr` of that statement is itself the identity. -/
theorem pullbackObjCongr_val_app_top {A D : Scheme.{u}} {g g' : A ⟶ D} (h : g = g')
    (N : D.Modules) (t : Γ(N, (⊤ : D.Opens))) :
    (((AffineShape.pullbackObjCongr h N).hom.val.app (.op ⊤)).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app
          (.op ⊤)).hom t)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app N).val.app (.op ⊤)).hom t := by
  subst h
  rfl


/-! ### The source-slot junction on global sections -/

/-- **The source-slot junction on global sections.** For the part (2) presentation data of
[Stacks, Tag 01R3], a global section `x` of the affine model's ideal sheaf and a global section
`y` of the ideal sheaf of `j ∣_ V` whose image in the structure sheaf is the one `x` has,
transported by the comorphism of `AlgebraicGeometry.IsAffineOpen.isoSpec`, the junction
`idealSheafIsoAffineModelOfMorphismRestrict` carries `y` to the unit generator attached to `x`.

`Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare_unit` describes
the junction's *inverse* through the inclusions of the two ideal sheaves; the hypothesis `hxy`
says `y` is the section that description produces, and
`Stacks.Conormal.Locality.idealSheaf_section_injective` makes that identification, the inclusion
of an ideal sheaf being a monomorphism. -/
theorem junction_val_app_top {A B : Scheme.{u}} (j : A ⟶ B) (V : B.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ(B, V)) (e : Limits.pullback j V.ι ≅ Spec (.of (Γ(B, V) ⧸ I)))
    (he : Limits.pullback.snd j V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (x : Γ(Stacks.ClosedImmersion.idealSheaf
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom, ⊤))
    (y : Γ(Stacks.ClosedImmersion.idealSheaf (j ∣_ V).toLRSHom.toShHom, ⊤))
    (hxy : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom (j ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom y =
          ((SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom hV.isoSpec.hom.toLRSHom.toShHom)).val.app (.op ⊤)).hom
            (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)
                )).val.app (.op ⊤)).hom x)) :
    ((AffineCotangent.SourceTransport.idealSheafIsoAffineModelOfMorphismRestrict
          j V hV I e he).hom.val.app (.op ⊤)).hom y =
      (((Scheme.Modules.pullbackPushforwardAdjunction hV.isoSpec.hom).unit.app
        (Stacks.ClosedImmersion.idealSheaf
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)).val.app
            (.op ⊤)).hom x := by
  have hunit := AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare_unit
    (j ∣_ V) ((pullbackRestrictIsoRestrict j V).symm ≪≫ e)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) hV.isoSpec
    (AffineShape.morphismRestrict_isoSpec_eq j V hV I e he)
  have h1 := congrArg (fun g => ModuleCat.Hom.hom g x) (congr($(hunit).val.app (.op ⊤)))
  have h2 : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (j ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom
        (((AffineCotangent.SourceTransport.idealSheafIsoAffineModelOfMorphismRestrict
            j V hV I e he).inv.val.app (.op ⊤)).hom
          ((((Scheme.Modules.pullbackPushforwardAdjunction hV.isoSpec.hom).unit.app
            (Stacks.ClosedImmersion.idealSheaf
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)).val.app
                (.op ⊤)).hom x)) =
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (j ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom y :=
    h1.trans hxy.symm
  have h3 := Locality.idealSheaf_section_injective (j ∣_ V) ⊤ h2
  refine Eq.trans (congrArg (fun z =>
    ((AffineCotangent.SourceTransport.idealSheafIsoAffineModelOfMorphismRestrict
      j V hV I e he).hom.val.app (.op ⊤)).hom z) h3.symm) ?_
  exact congrArg (fun g => ModuleCat.Hom.hom g _)
    (congr($((AffineCotangent.SourceTransport.idealSheafIsoAffineModelOfMorphismRestrict
      j V hV I e he).inv_hom_id).val.app (.op ⊤)))


/-! ### The engine on global sections -/

/-- **The generator formula for the part (2) engine of [Stacks, Tag 01R3].** Let `j : A ⟶ B` be a
morphism of schemes, `M` a module on `A`, and `I, e, he` the presentation data at an affine open
`V` of `B`. Let `c` be a locality comparison identifying `M ∣_ (j ⁻¹ᵁ V)` with the inverse image
along `j ∣_ V` of the ideal sheaf of `j ∣_ V`, and suppose — this is `hc`, the one further
argument the engine's own docstring says it needs — that `c` carries the restriction of a section
`m` of `j _* M` over `V` to the unit generator attached to a section `y` of the ideal sheaf of
`j ∣_ V`. Suppose further that `y` and a section `x` of the affine model's ideal sheaf have the
same image in the structure sheaf, up to the comorphism of
`AlgebraicGeometry.IsAffineOpen.isoSpec`.

Then over the top open the engine carries `m` to the unit generator attached to `x`.

So the quotient generators of [Stacks, Tag 01R3] are carried to the unit generators that the
affine model's own generator formula is stated at, which is the whole content of the part (2)
passage. See the module docstring for the four tooling facts the assembly rests on. -/
theorem restrictAffineModelIso_val_app_top {A B : Scheme.{u}} (j : A ⟶ B) (M : A.Modules)
    (V : B.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(B, V))
    (e : Limits.pullback j V.ι ≅ Spec (.of (Γ(B, V) ⧸ I)))
    (he : Limits.pullback.snd j V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (c : (Scheme.Modules.restrictFunctor (j ⁻¹ᵁ V).ι).obj M ≅
      (modulePullback (j ∣_ V).toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf (j ∣_ V).toLRSHom.toShHom))
    (x : Γ(Stacks.ClosedImmersion.idealSheaf
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom, ⊤))
    (y : Γ(Stacks.ClosedImmersion.idealSheaf (j ∣_ V).toLRSHom.toShHom, ⊤))
    (hxy : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom (j ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom y =
          ((SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom hV.isoSpec.hom.toLRSHom.toShHom)).val.app (.op ⊤)).hom
            (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)
                )).val.app (.op ⊤)).hom x))
    (m : Γ((Scheme.Modules.pushforward j ⋙ Scheme.Modules.restrictFunctor V.ι).obj M,
      (⊤ : V.toScheme.Opens)))
    (hc : (c.hom.val.app (.op ⊤)).hom
            ((((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso
              j V).app M).hom.val.app (.op ⊤)).hom m) =
          (((Scheme.Modules.pullbackPushforwardAdjunction (j ∣_ V)).unit.app
            (Stacks.ClosedImmersion.idealSheaf (j ∣_ V).toLRSHom.toShHom)).val.app
              (.op ⊤)).hom y) :
    ((CotangentAppIso.restrictAffineModelIso j M V hV I e he c).hom.val.app (.op ⊤)).hom m =
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).unit.app
          (Stacks.ClosedImmersion.idealSheaf
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)).val.app
              (.op ⊤)).hom x := by
  iterate 4 refine Eq.trans (trans_val_app _ _ _ _) ?_
  refine Eq.trans (pushforwardComp_inv_val_app _ _ _ _ _) ?_
  refine Eq.trans (pushforwardCongr_val_app_top
    (CotangentAppIso.isoSpec_inv_comp_eq j V hV I e he) _ _) ?_
  refine Eq.trans (pushforwardComp_val_app _ _ _ _ _) ?_
  refine Eq.trans (pushforward_mapIso_val_app_top _ _ _) ?_
  iterate 4 refine Eq.trans (trans_val_app _ _ _ _) ?_
  refine Eq.trans (trans_val_app _ _ _ _) ?_
  simp only [hc]
  refine Eq.trans
    (congrArg (fun a => ((Iso.hom (C := Scheme.Modules _) _).val.app (.op _)).hom a)
    (congrArg (fun a => ((Iso.hom (C := Scheme.Modules _) _).val.app (.op _)).hom a)
    (congrArg (fun a => ((Iso.hom (C := Scheme.Modules _) _).val.app (.op _)).hom a)
    (congrArg (fun a => ((Iso.hom (C := Scheme.Modules _) _).val.app (.op _)).hom a)
    ((pullback_mapIso_unit_val_app_top (j ∣_ V)
      (AffineCotangent.SourceTransport.idealSheafIsoAffineModelOfMorphismRestrict
        j V hV I e he) y).trans
      (congrArg (fun a => (((Scheme.Modules.pullbackPushforwardAdjunction (j ∣_ V)).unit.app
          _).val.app (.op ⊤)).hom a)
        (junction_val_app_top j V hV I e he x y hxy))))))) ?_
  refine Eq.trans
    (congrArg (fun a => ((Iso.hom (C := Scheme.Modules _) _).val.app (.op _)).hom a)
    (congrArg (fun a => ((Iso.hom (C := Scheme.Modules _) _).val.app (.op _)).hom a)
    (congrArg (fun a => ((Iso.hom (C := Scheme.Modules _) _).val.app (.op _)).hom a)
    (PullbackPseudofunctor.unit_comp_map_modulePullbackCompIso_inv_app hV.isoSpec.hom (j ∣_ V)
      (Stacks.ClosedImmersion.idealSheaf
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom) ⊤ x)))) ?_
  refine Eq.trans
    (congrArg (fun a => ((Iso.hom (C := Scheme.Modules _) _).val.app (.op _)).hom a)
    (congrArg (fun a => ((Iso.hom (C := Scheme.Modules _) _).val.app (.op _)).hom a)
    (pullbackObjCongr_val_app_top (AffineShape.morphismRestrict_isoSpec_eq j V hV I e he)
      (Stacks.ClosedImmersion.idealSheaf
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom) x))) ?_
  refine Eq.trans
    (congrArg (fun a => ((Iso.hom (C := Scheme.Modules _) _).val.app (.op _)).hom a)
    (PullbackPseudofunctor.unit_comp_map_modulePullbackCompIso_app
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      ((pullbackRestrictIsoRestrict j V).symm ≪≫ e).hom
      (Stacks.ClosedImmersion.idealSheaf
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom) ⊤ x)) ?_
  exact AffineShape.pullbackIsoPushforwardInv_hom_val_app_top _ _ _


/-! ### The part (2) identification on sections, with the generator formula -/

/-- A composite of isomorphisms of modules over a fixed ring, on an element. -/
theorem trans_apply {R : CommRingCat.{u}} {P Q S : ModuleCat.{u} R} (p : P ≅ Q) (q : Q ≅ S)
    (z : P) : (p ≪≫ q).hom.hom z = q.hom.hom (p.hom.hom z) :=
  rfl

/-- The engine read through `CategoryTheory.SheafOfModules.evaluation` and a restriction of
scalars is the engine read on sections: neither functor moves an element. -/
theorem evaluation_mapIso_apply {A B : Scheme.{u}} (j : A ⟶ B) (M : A.Modules) (V : B.Opens)
    (hV : IsAffineOpen V) (I : Ideal Γ(B, V))
    (e : Limits.pullback j V.ι ≅ Spec (.of (Γ(B, V) ⧸ I)))
    (he : Limits.pullback.snd j V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (c : (Scheme.Modules.restrictFunctor (j ⁻¹ᵁ V).ι).obj M ≅
      (modulePullback (j ∣_ V).toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf (j ∣_ V).toLRSHom.toShHom))
    (z : (ModuleCat.restrictScalars V.topIso.inv.hom).obj
      (((Scheme.Modules.restrictFunctor V.ι).obj
        ((Scheme.Modules.pushforward j).obj M)).val.obj (.op ⊤))) :
    (((ModuleCat.restrictScalars V.topIso.inv.hom).mapIso
        ((SheafOfModules.evaluation V.toScheme.ringCatSheaf (.op ⊤)).mapIso
          (CotangentAppIso.restrictAffineModelIso j M V hV I e he c))).hom).hom z =
      ((CotangentAppIso.restrictAffineModelIso j M V hV I e he c).hom.val.app (.op ⊤)).hom z :=
  rfl

/-- **The generator formula for the part (2) identification of [Stacks, Tag 01R3].** With the
data of `restrictAffineModelIso_val_app_top` and a section `x` of the affine model's ideal sheaf
whose image in the structure sheaf is `a ∈ I`, the `Γ(B, V)`-module isomorphism
`Stacks.Conormal.CotangentAppIso.affineSectionsIsoCotangent` carries the section `s` of `j _* M`
over `V` to `I.toCotangent a`.

This is the formula on ideal generators that
`StacksFrontier.AlgebraicGeometry.CotangentAppIso.Sections` records as absent, and it needs no
new identification: `affineSectionsIsoCotangent` is built from
`Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent`'s `.choose`, and that existential's
`.choose_spec` *is* the formula, discarded only because nothing could be said about the engine.
The three remaining factors are a restriction map
(`Stacks.Conormal.CotangentAppIso.sectionsRestrictTopIso_hom_apply`) and two changes of scalars
that do not move an element (`isoSpecPushforwardTopSectionsIso_hom_apply` and
`evaluation_mapIso_apply`). -/
theorem affineSectionsIsoCotangent_apply {A B : Scheme.{u}} (j : A ⟶ B)
    (M : A.Modules) (V : B.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(B, V))
    (e : Limits.pullback j V.ι ≅ Spec (.of (Γ(B, V) ⧸ I)))
    (he : Limits.pullback.snd j V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (c : (Scheme.Modules.restrictFunctor (j ⁻¹ᵁ V).ι).obj M ≅
      (modulePullback (j ∣_ V).toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf (j ∣_ V).toLRSHom.toShHom))
    (a : I)
    (x : Γ(Stacks.ClosedImmersion.idealSheaf
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom, ⊤))
    (y : Γ(Stacks.ClosedImmersion.idealSheaf (j ∣_ V).toLRSHom.toShHom, ⊤))
    (s : ((Scheme.Modules.pushforward j).obj M).val.obj (.op V))
    (hxy : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom (j ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom y =
          ((SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom hV.isoSpec.hom.toLRSHom.toShHom)).val.app (.op ⊤)).hom
            (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)
                )).val.app (.op ⊤)).hom x))
    (hax : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)
            )).val.app (.op ⊤)).hom x = (Scheme.ΓSpecIso Γ(B, V)).inv (a : Γ(B, V)))
    (hc : (c.hom.val.app (.op ⊤)).hom
            ((((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso
              j V).app M).hom.val.app (.op ⊤)).hom
              ((((Scheme.Modules.pushforward j).obj M).val.map
                (eqToHom V.ι_image_top).op).hom s)) =
          (((Scheme.Modules.pullbackPushforwardAdjunction (j ∣_ V)).unit.app
            (Stacks.ClosedImmersion.idealSheaf (j ∣_ V).toLRSHom.toShHom)).val.app
              (.op ⊤)).hom y) :
    (CotangentAppIso.affineSectionsIsoCotangent j M V hV I e he c).hom.hom s =
      I.toCotangent a := by
  refine Eq.trans (trans_apply _ _ s) ?_
  refine Eq.trans (congrArg (fun z => (((ModuleCat.restrictScalars V.topIso.inv.hom).mapIso
      ((SheafOfModules.evaluation V.toScheme.ringCatSheaf (.op ⊤)).mapIso
        (CotangentAppIso.restrictAffineModelIso j M V hV I e he c)) ≪≫
      CotangentAppIso.isoSpecPushforwardTopSectionsIso V hV _ ≪≫
      (AffineModel.exists_idealSheafΓIsoCotangent Γ(B, V) I).choose).hom).hom z)
    (CotangentAppIso.sectionsRestrictTopIso_hom_apply
      ((Scheme.Modules.pushforward j).obj M) V s)) ?_
  refine Eq.trans (trans_apply _ _ _) ?_
  refine Eq.trans (congrArg (fun z => ((CotangentAppIso.isoSpecPushforwardTopSectionsIso V hV _ ≪≫
      (AffineModel.exists_idealSheafΓIsoCotangent Γ(B, V) I).choose).hom).hom z)
    (evaluation_mapIso_apply j M V hV I e he c _)) ?_
  refine Eq.trans (trans_apply _ _ _) ?_
  refine Eq.trans (congrArg
    (fun z => (AffineModel.exists_idealSheafΓIsoCotangent Γ(B, V) I).choose.hom.hom z)
    (CotangentAppIso.isoSpecPushforwardTopSectionsIso_hom_apply V hV _ _)) ?_
  refine Eq.trans (congrArg
    (fun z => (AffineModel.exists_idealSheafΓIsoCotangent Γ(B, V) I).choose.hom.hom z)
    (restrictAffineModelIso_val_app_top j M V hV I e he c x y hxy _ hc)) ?_
  exact (AffineModel.exists_idealSheafΓIsoCotangent Γ(B, V) I).choose_spec a x hax

end Stacks.Conormal.CotangentAppIsoGenerator

end
