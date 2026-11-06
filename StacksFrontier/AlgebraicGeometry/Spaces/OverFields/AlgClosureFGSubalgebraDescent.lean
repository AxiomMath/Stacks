module

public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GaloisBaseChangeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteEnlargement
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStage
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrictProduct

/-!
# The descent situation of the finitely generated subalgebras of a field extension

Let `k` be a field, `K/k` a field extension and `X` a quasi-compact and quasi-separated
algebraic space over `k`, all inside a chosen big fppf site. Writing `K` as the filtered union
of its finitely generated `k`-subalgebras `A` and putting `X_A = X ×_{Spec k} Spec A` presents
`X_K` as the limit of a directed inverse system of quasi-compact and quasi-separated algebraic
spaces with affine transition morphisms, that is as an
`AlgebraicGeometry.Space.DescentSituation`. This is the engine of [Stacks, Tag 0B84] part (2):
once `X_K` is a scheme, the limit of that system is representable, so some stage `X_A` is a
scheme, and a residue field of `A` at a maximal ideal is a finite extension of `k` by Hilbert's
Nullstellensatz.

This file builds that descent situation and the two identifications a consumer of it needs: of
the limit of the system with the base change `X_K`, and of a stage with the base change `X_A`.

## Main definitions

* `AlgebraicGeometry.Space.fgSubalgebraSiteDiagram`: the cofiltered diagram of the spectra of
  the finitely generated `k`-subalgebras of `K`, as objects of the big fppf site of `Spec k`,
  with `Spec K` as its limit (`AlgebraicGeometry.Space.isLimitFgSubalgebraSiteCone`).
* `AlgebraicGeometry.Space.fgSubalgebraSystem`: the system `A ↦ X_A` of base changes of `X`,
  with its chosen limit cone `AlgebraicGeometry.Space.fgSubalgebraSystemLimitCone`.
* `AlgebraicGeometry.Space.fgSubalgebraDescentSituation`: **the descent situation itself.**

## Main results

* `AlgebraicGeometry.Space.fgSubalgebraSystemObjIso` and
  `AlgebraicGeometry.Space.extensionBaseChangeIsoLimitConePt`: a stage of the system is the
  base change `X_A` and the limit of the system is the base change `X_K`, both in the form
  `AlgebraicGeometry.Space.extensionBaseChange` uses, namely the product with the presheaf
  represented by the spectrum.
* `AlgebraicGeometry.Space.isRepresentable_limitCone_pt_of_isRepresentable_relocalizeRestrict`:
  if `X_K` is a scheme over `Spec K` then the limit of the system is representable. This is the
  hypothesis a consumer of the descent situation has to feed it.
* `AlgebraicGeometry.Space.isRepresentable_relocalizeRestrict_of_isRepresentable_system_obj`:
  if a stage of the system is representable over `Spec k` then `X_A` is a scheme over
  `Spec A`. This is how the conclusion of such a consumer is read back out.
* `AlgebraicGeometry.Space.exists_fgSubalgebra_isRepresentable_relocalizeRestrict`: if `X_K` is
  a scheme then so is `X_A` for some finitely generated `k`-subalgebra `A` of `K`, on an
  arbitrary big fppf site; this is [Stacks, Tag 07SR] applied to the situation, on an enlargement
  of the site where the finitely generated subalgebras of `K` are fewer than the cofinality of
  the cutoff.

## Implementation notes

The algebra-level and scheme-level halves of the presentation are not rebuilt here: the
directed index `AlgebraicGeometry.FieldExtensionDescent.FGSubalgebra`, the diagram of spectra
`AlgebraicGeometry.FieldExtensionDescent.specDiagram` and its limit cone
`AlgebraicGeometry.FieldExtensionDescent.specLimitCone` over `Spec k` are taken from
`StacksFrontier/AlgebraicGeometry/FieldExtensionDescent/Limit.lean`. What is added is the passage
to the site and to presheaves:

* the spectrum of a subalgebra of `K` lies in the site because it injects into `K`, so the
  scheme-level diagram lifts to the site's underlying full subcategory, and the structure
  morphisms over `Spec k` lift it further to the site of `Spec k` with
  `CategoryTheory.Over.lift`;
* its limit cone is the lifted one: the inclusion of the site's underlying category into all
  schemes is fully faithful, hence reflects limits, and `CategoryTheory.Over.isLimitLiftCone`
  adds the structure morphism back — the index category is nonempty, which is what that lemma
  needs;
* `Spec k` is terminal in its own big fppf site, so the base change of `X` to a stage is the
  fibre product of that stage with `X` over the terminal presheaf
  (`AlgebraicGeometry.Space.isTerminal_yoneda_obj_base`); the system is therefore
  `CategoryTheory.Over.pullback` of the lifted presheaf diagram, and both that functor, being a
  right adjoint, and `CategoryTheory.Over.forget`, the index category being connected, preserve
  the limit.

Both identifications of a base change are instances of
`AlgebraicGeometry.Space.isPullback_prod_fst_snd_yoneda_obj`: the fibre product over the
terminal presheaf *is* the product. The identification of the limit with `X_K` read over
`Spec K`, which is the one a consumer needs, is not an isomorphism of presheaves — the two live
on different sites — but an implication between representability statements, proved from
`CategoryTheory.OverShriek.relocalizeRestrictIsoProduct` and
`AlgebraicGeometry.Space.relocalizedYonedaRepresentableBy`.

No `@[stacks]` attribute is attached: Tag 0B84 asserts that an algebraic space which becomes a
scheme after some field extension becomes one after a finite separable extension, and that is
proved in `StacksFrontier/AlgebraicGeometry/Spaces/OverFields/AlgClosureSchemeDescent.lean`.

## References

* [Stacks Project, Tag 0B84](https://stacks.math.columbia.edu/tag/0B84)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open FieldExtensionDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (B : BigFppfSite.{u})

/-! ### The spectra of the finitely generated subalgebras as objects of the site -/

/-- **The spectrum of a `k`-subalgebra of `K` lies in the site as soon as `Spec K` does.** The
subalgebra injects into `K`, so its cardinality is below the cutoff of the site. -/
theorem contains_spec_subalgebra (hK : B.Contains (Spec (.of K))) (A : Subalgebra k K) :
    B.Contains (Spec (.of A)) :=
  B.contains_spec_of_mk_lt_cutoff
    (lt_of_le_of_lt (Cardinal.mk_le_of_injective (α := A) (β := K) Subtype.val_injective)
      (B.mk_lt_cutoff_of_contains_spec hK))

/-- The morphism `Spec K ⟶ Spec k` of the site underlying
`AlgebraicGeometry.Space.specExtension`, the apex of the limit cone below, is the lift of
`Spec (algebraMap k K)` to the site. Any other lift of that morphism of schemes — for instance
`AlgebraicGeometry.Space.fieldExtensionMap` — equals it, the inclusion of the site being
faithful. -/
theorem map_specExtensionHom (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) :
    B.inclusion.map (specExtensionHom k K B hk hK) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) :=
  rfl

/-- The morphism `Spec A ⟶ Spec k` of the site attached to a finitely generated
`k`-subalgebra `A` of `K`. -/
def fgSubalgebraSiteHom (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (A : FGSubalgebra k K) :
    B.obj (contains_spec_subalgebra k K B hK (A : Subalgebra k K)) ⟶ B.obj hk :=
  ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k (A : Subalgebra k K))))

/-- `Spec A`, viewed as an object of the big fppf site of `Spec k`, for a finitely generated
`k`-subalgebra `A` of `K`. -/
def fgSubalgebraSiteObj (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (A : FGSubalgebra k K) : BigFppfOver B (Spec (.of k)) hk :=
  Over.mk (fgSubalgebraSiteHom k K B hk hK A)

/-- The diagram of the spectra of the finitely generated `k`-subalgebras of `K` in the
underlying category of the site: the scheme-level diagram
`AlgebraicGeometry.FieldExtensionDescent.specDiagram`, each of whose values lies in the
site. -/
def fgSubalgebraSchemeDiagram (hK : B.Contains (Spec (.of K))) :
    (FGSubalgebra k K)ᵒᵖ ⥤ B.Schemes :=
  (schemeSizeBelow B.cutoff).lift (specDiagram k K ⋙ Over.forget (Spec (.of k)))
    fun i => contains_spec_subalgebra k K B hK (i.unop : Subalgebra k K)

/-- The structure morphisms of the spectra of the subalgebras over `Spec k`, as a natural
transformation from the diagram in the site's underlying category to the constant functor. -/
def fgSubalgebraSchemeToBase (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) :
    fgSubalgebraSchemeDiagram k K B hK ⟶
      (Functor.const (FGSubalgebra k K)ᵒᵖ).obj (B.obj hk) where
  app i := ObjectProperty.homMk ((specDiagram k K).obj i).hom
  naturality i j f := by
    apply B.inclusion.map_injective
    simp only [Functor.map_comp, Functor.const_obj_map]
    exact Over.w ((specDiagram k K).map f)

/-- The cofiltered diagram of the spectra of the finitely generated `k`-subalgebras of `K`, as
objects of the big fppf site of `Spec k`. -/
def fgSubalgebraSiteDiagram (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) :
    (FGSubalgebra k K)ᵒᵖ ⥤ BigFppfOver B (Spec (.of k)) hk :=
  Over.lift (fgSubalgebraSchemeDiagram k K B hK) (fgSubalgebraSchemeToBase k K B hk hK)

/-- A stage of the diagram in the site is `Spec A` with its structure morphism to
`Spec k`. -/
theorem fgSubalgebraSiteDiagram_obj (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (A : FGSubalgebra k K) :
    (fgSubalgebraSiteDiagram k K B hk hK).obj (op A) = fgSubalgebraSiteObj k K B hk hK A :=
  rfl

/-- The cone in the site's underlying category over the diagram of spectra of subalgebras,
with apex `Spec K`: the legs are the morphisms of spectra induced by the inclusions of the
subalgebras into `K`. -/
def fgSubalgebraSchemeCone (hK : B.Contains (Spec (.of K))) :
    Cone (fgSubalgebraSchemeDiagram k K B hK) where
  pt := B.obj hK
  π :=
    { app := fun i => ObjectProperty.homMk ((specLimitCone k K).cone.π.app i).left
      naturality := fun i j f => by
        apply B.inclusion.map_injective
        simp only [Functor.map_comp, Functor.const_obj_map]
        exact (congrArg Over.Hom.left ((specLimitCone k K).cone.w f)).symm }

/-- **`Spec K` is the limit of the spectra of the finitely generated `k`-subalgebras of `K`
inside the site.** The inclusion of the site's underlying category into all schemes is fully
faithful, so it reflects limits, and the limit of the diagram of schemes is
`AlgebraicGeometry.FieldExtensionDescent.specLimitCone` with its structure morphism
forgotten. -/
def isLimitFgSubalgebraSchemeCone (hK : B.Contains (Spec (.of K))) :
    IsLimit (fgSubalgebraSchemeCone k K B hK) := by
  apply isLimitOfReflects B.inclusion
  exact IsLimit.ofIsoLimit (isLimitOfPreserves (Over.forget (Spec (.of k)))
    (specLimitCone k K).isLimit)
    (Cone.ext (Iso.refl _) fun i => by
      simp only [Iso.refl_hom]
      rfl)

/-- The cone over the diagram in the site of `Spec k` with apex `Spec K`, viewed over
`Spec k`. -/
def fgSubalgebraSiteCone (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K))) :
    Cone (fgSubalgebraSiteDiagram k K B hk hK) :=
  Over.liftCone (fgSubalgebraSchemeDiagram k K B hK) (fgSubalgebraSchemeToBase k K B hk hK)
    (fgSubalgebraSchemeCone k K B hK) (specExtensionHom k K B hk hK)
    fun i => by
      apply B.inclusion.map_injective
      simp only [Functor.map_comp]
      exact Over.w ((specLimitCone k K).cone.π.app i)

/-- The apex of that cone is `Spec K` over `Spec k`, that is
`AlgebraicGeometry.Space.specExtension`. -/
theorem fgSubalgebraSiteCone_pt (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) :
    (fgSubalgebraSiteCone k K B hk hK).pt = specExtension k K B hk hK :=
  rfl

/-- **`Spec K` over `Spec k` is the limit of the spectra of the finitely generated
`k`-subalgebras of `K` in the big fppf site of `Spec k`.** The limit in the underlying category
is `AlgebraicGeometry.Space.isLimitFgSubalgebraSchemeCone`, and a limit of a diagram of objects
over a base is computed on underlying objects as soon as the index category is nonempty. -/
def isLimitFgSubalgebraSiteCone (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) : IsLimit (fgSubalgebraSiteCone k K B hk hK) :=
  haveI : Nonempty (FGSubalgebra k K)ᵒᵖ := ⟨op ⟨⊥, Subalgebra.fg_bot⟩⟩
  Over.isLimitLiftCone (fgSubalgebraSchemeDiagram k K B hK)
    (fgSubalgebraSchemeToBase k K B hk hK) (fgSubalgebraSchemeCone k K B hK)
    (specExtensionHom k K B hk hK) _ (isLimitFgSubalgebraSchemeCone k K B hK)

/-! ### The system of base changes -/

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on a big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_AlgClosureFGSubalgebraDescent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_AlgClosureFGSubalgebraDescent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_AlgClosureFGSubalgebraDescent.has_limit _

set_option synthInstance.maxHeartbeats 400000

/-- The diagram of the presheaves represented by the spectra of the finitely generated
`k`-subalgebras of `K`. -/
def fgSubalgebraPresheafDiagram (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) :
    (FGSubalgebra k K)ᵒᵖ ⥤ ((BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :=
  fgSubalgebraSiteDiagram k K B hk hK ⋙ yoneda

/-- The structure morphisms of the presheaf diagram over the presheaf represented by the base,
which is a terminal presheaf. -/
def fgSubalgebraPresheafToBase (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) :
    fgSubalgebraPresheafDiagram k K B hk hK ⟶
      (Functor.const (FGSubalgebra k K)ᵒᵖ).obj (yoneda.obj (Over.mk (𝟙 (B.obj hk)))) where
  app i := yoneda.map (Over.mkIdTerminal.from ((fgSubalgebraSiteDiagram k K B hk hK).obj i))
  naturality _ _ _ := (isTerminal_yoneda_obj_base B (Spec (.of k)) hk).hom_ext _ _

/-- **The system of base changes `A ↦ X_A = X ×_{Spec k} Spec A`** of an algebraic space `X`
over `k` to the finitely generated `k`-subalgebras of `K`. The base `Spec k` is terminal in its
own big fppf site, so the base change is the fibre product over the terminal presheaf. -/
def fgSubalgebraSystem (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    (FGSubalgebra k K)ᵒᵖ ⥤ ((BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :=
  Over.lift (fgSubalgebraPresheafDiagram k K B hk hK) (fgSubalgebraPresheafToBase k K B hk hK) ⋙
    Over.pullback ((isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from X) ⋙ Over.forget X

set_option maxHeartbeats 1000000 in
/-- A stage of the system is the fibre product of the presheaf represented by `Spec A` with
`X` over the terminal presheaf. -/
theorem fgSubalgebraSystem_obj (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (A : FGSubalgebra k K) :
    (fgSubalgebraSystem k K B hk hK X).obj (op A) =
      Limits.pullback (yoneda.map (Over.mkIdTerminal.from (fgSubalgebraSiteObj k K B hk hK A)))
        ((isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from X) :=
  rfl

set_option maxHeartbeats 1000000 in
/-- **A stage of the system is the base change `X_A`**, in the form of the product with the
presheaf represented by `Spec A` — which is what
`AlgebraicGeometry.Space.extensionBaseChange` is for a field extension. -/
def fgSubalgebraSystemObjIso (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (A : FGSubalgebra k K) :
    yoneda.obj (fgSubalgebraSiteObj k K B hk hK A) ⨯ X ≅
      (fgSubalgebraSystem k K B hk hK X).obj (op A) :=
  (isPullback_prod_fst_snd_yoneda_obj (fgSubalgebraSiteObj k K B hk hK A) X).isoPullback

/-- **`X_K` is the limit of the system of base changes `X_A`.** The presheaf diagram has
`Spec K` as its limit over `Spec k`, base change along the structure morphism of `X` is a right
adjoint, and forgetting the structure morphism preserves a limit over a connected index. -/
def fgSubalgebraSystemLimitCone (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    LimitCone (fgSubalgebraSystem k K B hk hK X) where
  cone :=
    (Over.forget X).mapCone
      ((Over.pullback ((isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from X)).mapCone
        (Over.liftCone (fgSubalgebraPresheafDiagram k K B hk hK)
          (fgSubalgebraPresheafToBase k K B hk hK)
          (yoneda.mapCone (fgSubalgebraSiteCone k K B hk hK))
          (yoneda.map (Over.mkIdTerminal.from (specExtension k K B hk hK)))
          fun _ => (isTerminal_yoneda_obj_base B (Spec (.of k)) hk).hom_ext _ _))
  isLimit :=
    haveI : Nonempty (FGSubalgebra k K)ᵒᵖ := ⟨op ⟨⊥, Subalgebra.fg_bot⟩⟩
    isLimitOfPreserves _ (isLimitOfPreserves _
      (Over.isLimitLiftCone (fgSubalgebraPresheafDiagram k K B hk hK)
        (fgSubalgebraPresheafToBase k K B hk hK)
        (yoneda.mapCone (fgSubalgebraSiteCone k K B hk hK))
        (yoneda.map (Over.mkIdTerminal.from (specExtension k K B hk hK))) _
        (isLimitOfPreserves yoneda (isLimitFgSubalgebraSiteCone k K B hk hK))))

set_option maxHeartbeats 1000000 in
/-- The apex of the chosen limit cone is the fibre product of the presheaf represented by
`Spec K` with `X` over the terminal presheaf. -/
theorem fgSubalgebraSystemLimitCone_pt (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    (fgSubalgebraSystemLimitCone k K B hk hK X).cone.pt =
      Limits.pullback (yoneda.map (Over.mkIdTerminal.from (specExtension k K B hk hK)))
        ((isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from X) :=
  rfl

set_option maxHeartbeats 1000000 in
/-- **The limit of the system is the base change `X_K`**, in the form
`AlgebraicGeometry.Space.extensionBaseChange` uses. -/
def extensionBaseChangeIsoLimitConePt (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    extensionBaseChange k K B hk hK X ≅ (fgSubalgebraSystemLimitCone k K B hk hK X).cone.pt :=
  (isPullback_prod_fst_snd_yoneda_obj (specExtension k K B hk hK) X).isoPullback

/-! ### The stages of the system -/

/-- The scheme underlying a stage of the diagram in the site is affine, being the spectrum of
the subalgebra. -/
theorem isAffine_toScheme_fgSubalgebraSiteObj (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (A : FGSubalgebra k K) :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
      (fgSubalgebraSiteObj k K B hk hK A)) := by
  show IsAffine (Spec (.of (A : Subalgebra k K)))
  infer_instance

/-- The scheme underlying a stage of the diagram in the site is affine. This is the previous
statement at the stage of the diagram rather than at
`AlgebraicGeometry.Space.fgSubalgebraSiteObj`, which is the spelling instance search needs. -/
theorem isAffine_toScheme_fgSubalgebraSiteDiagram_obj (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (i : (FGSubalgebra k K)ᵒᵖ) :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
      ((fgSubalgebraSiteDiagram k K B hk hK).obj i)) :=
  isAffine_toScheme_fgSubalgebraSiteObj k K B hk hK i.unop

/-- The scheme underlying the terminal object of the site of `Spec k` is `Spec k`, which is
affine. -/
theorem isAffine_toScheme_mk_id (hk : B.Contains (Spec (.of k))) :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (Over.mk (𝟙 (B.obj hk)))) := by
  show IsAffine (Spec (.of k))
  infer_instance

/-- A representable presheaf on the site of `Spec k` whose scheme is affine is absolutely
quasi-separated: an affine scheme is quasi-separated, so [Stacks, Tag 03JX] applies. -/
theorem isAbsolutelyQuasiSeparated_yoneda_obj_of_isAffine (hk : B.Contains (Spec (.of k)))
    (U : BigFppfOver B (Spec (.of k)) hk)
    (hU : IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U)) :
    IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal (yoneda.obj U) :=
  have := hU
  isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (Spec (.of k)) hk (yoneda.obj U)
    B.contains_terminal ⟨U, inferInstance, ⟨Functor.RepresentableBy.yoneda U⟩⟩

/-- The fibre product over the terminal presheaf of a representable presheaf with an algebraic
space is an algebraic space, by [Stacks, Tag 02X2]. -/
private theorem isAlgebraicSpace_pullback_yoneda_map_from (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (T : BigFppfOver B (Spec (.of k)) hk) :
    IsAlgebraicSpace B (Spec (.of k)) hk
      (pullback (yoneda.map (Over.mkIdTerminal.from T))
        ((isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from X)) :=
  isAlgebraicSpace_pullback B (Spec (.of k)) hk _ _
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk T) hX
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (Over.mk (𝟙 (B.obj hk))))

/-- Each stage of the system is an algebraic space over `Spec k`, being a fibre product of
algebraic spaces by [Stacks, Tag 02X2]. -/
theorem isAlgebraicSpace_fgSubalgebraSystem_obj (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (A : FGSubalgebra k K) :
    IsAlgebraicSpace B (Spec (.of k)) hk ((fgSubalgebraSystem k K B hk hK X).obj (op A)) :=
  isAlgebraicSpace_pullback_yoneda_map_from k B hk X hX (fgSubalgebraSiteObj k K B hk hK A)

/-- Each stage of the system is quasi-compact by [Stacks, Tag 073B] part (3): it is the fibre
product of the quasi-compact `Spec A` with the quasi-compact `X` over the quasi-separated
`Spec k`. -/
theorem isQuasiCompactSpace_fgSubalgebraSystem_obj (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hXqc : IsQuasiCompactSpace B (Spec (.of k)) hk X) (A : FGSubalgebra k K) :
    IsQuasiCompactSpace B (Spec (.of k)) hk ((fgSubalgebraSystem k K B hk hK X).obj (op A)) :=
  isQuasiCompactSpace_pullback B (Spec (.of k)) hk B.contains_terminal _ _
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (fgSubalgebraSiteObj k K B hk hK A))
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (Over.mk (𝟙 (B.obj hk))))
    (isQuasiCompactSpace_yoneda_of_isAffine B (Spec (.of k)) hk
      (fgSubalgebraSiteObj k K B hk hK A) (isAffine_toScheme_fgSubalgebraSiteObj k K B hk hK A))
    hXqc
    (isAbsolutelyQuasiSeparated_yoneda_obj_of_isAffine k B hk (Over.mk (𝟙 (B.obj hk)))
      (isAffine_toScheme_mk_id k B hk))

/-- Each stage of the system is quasi-separated by [Stacks, Tag 073B] part (3): it is the fibre
product of the quasi-separated `Spec A` with the quasi-separated `X`. -/
theorem isAbsolutelyQuasiSeparated_fgSubalgebraSystem_obj (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X)
    (A : FGSubalgebra k K) :
    IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal
      ((fgSubalgebraSystem k K B hk hK X).obj (op A)) :=
  isAbsolutelyQuasiSeparated_pullback B (Spec (.of k)) hk B.contains_terminal _ _
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (fgSubalgebraSiteObj k K B hk hK A)) hX
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (Over.mk (𝟙 (B.obj hk))))
    (isAbsolutelyQuasiSeparated_yoneda_obj_of_isAffine k B hk
      (fgSubalgebraSiteObj k K B hk hK A) (isAffine_toScheme_fgSubalgebraSiteObj k K B hk hK A))
    hXqs

/-- The limit of the system is an algebraic space over `Spec k`, being a fibre product of
algebraic spaces. -/
theorem isAlgebraicSpace_fgSubalgebraSystemLimitCone_pt (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsAlgebraicSpace B (Spec (.of k)) hk (fgSubalgebraSystemLimitCone k K B hk hK X).cone.pt :=
  isAlgebraicSpace_pullback_yoneda_map_from k B hk X hX (specExtension k K B hk hK)

/-- **The transition morphisms of the system are affine.** A transition morphism is the base
change along the structure morphism of `X` of the morphism `Spec A' ⟶ Spec A` of spectra of
subalgebras, which is affine because both of its ends are; affineness of a morphism of
algebraic spaces is stable under base change by [Stacks, Tag 03WI]. -/
theorem isAffineHom_fgSubalgebraSystem_map (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    {i j : (FGSubalgebra k K)ᵒᵖ} (g : i ⟶ j) :
    IsAffineHom B (Spec (.of k)) hk ((fgSubalgebraSystem k K B hk hK X).map g) := by
  set p := (isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from X
  set t := fgSubalgebraPresheafToBase k K B hk hK
  set a := (fgSubalgebraPresheafDiagram k K B hk hK).map g
  have haAffine : IsAffineHom B (Spec (.of k)) hk a := by
    have := isAffine_toScheme_fgSubalgebraSiteDiagram_obj k K B hk hK i
    have := isAffine_toScheme_fgSubalgebraSiteDiagram_obj k K B hk hK j
    exact isAffineHom_of_presheaf
      ((presheaf_yoneda_map_iff B (Spec (.of k)) hk
          (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance
          ((fgSubalgebraSiteDiagram k K B hk hK).map g)).mpr
        (_root_.AlgebraicGeometry.isAffineHom_of_isAffine _))
  have hcomp : a ≫ t.app j = t.app i :=
    (isTerminal_yoneda_obj_base B (Spec (.of k)) hk).hom_ext _ _
  have hcond : (pullback.fst (t.app i) p ≫ a) ≫ t.app j = pullback.snd (t.app i) p ≫ p := by
    rw [Category.assoc, hcomp]
    exact pullback.condition
  have hfst : (fgSubalgebraSystem k K B hk hK X).map g ≫ pullback.fst (t.app j) p =
      pullback.fst (t.app i) p ≫ a :=
    pullback.lift_fst _ _ hcond
  have hsnd : (fgSubalgebraSystem k K B hk hK X).map g ≫ pullback.snd (t.app j) p =
      pullback.snd (t.app i) p :=
    pullback.lift_snd _ _ hcond
  have hPasted : IsPullback (pullback.fst (t.app i) p)
      ((fgSubalgebraSystem k K B hk hK X).map g ≫ pullback.snd (t.app j) p)
      (a ≫ t.app j) p :=
    (IsPullback.of_hasPullback (t.app i) p).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp)
      (by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        exact hsnd.symm)
      (by simp [hcomp]) (by simp)
  exact IsAffineHom.of_isPullback (IsPullback.of_isLimit
    (leftSquareIsPullback (PullbackCone.mk (pullback.fst (t.app i) p)
      ((fgSubalgebraSystem k K B hk hK X).map g) hfst.symm) rfl
      (pullback.isLimit (t.app j) p) hPasted.isLimit)) haAffine

/-! ### The descent situation -/

/-- **The descent situation of the finitely generated subalgebras of a field extension.** For a
quasi-compact and quasi-separated algebraic space `X` over a field `k` and a field extension
`K/k` inside a big fppf site, the base changes `X_A` of `X` to the finitely generated
`k`-subalgebras `A` of `K` form a directed inverse system of quasi-compact and quasi-separated
algebraic spaces with affine transition morphisms, whose limit is `X_K`.

This is the first half of the proof of [Stacks, Tag 0B84]; the chosen index is the zero
subalgebra, so a consumer of this situation produces an arbitrary stage. -/
def fgSubalgebraDescentSituation (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXqc : IsQuasiCompactSpace B (Spec (.of k)) hk X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X) :
    DescentSituation B (Spec (.of k)) hk B.contains_terminal (FGSubalgebra k K) where
  system := fgSubalgebraSystem k K B hk hK X
  algebraicSpace := isAlgebraicSpace_fgSubalgebraSystem_obj k K B hk hK X hX
  transition_affine g := isAffineHom_fgSubalgebraSystem_map k K B hk hK X g
  quasiCompact := isQuasiCompactSpace_fgSubalgebraSystem_obj k K B hk hK X hXqc
  quasiSeparated := isAbsolutelyQuasiSeparated_fgSubalgebraSystem_obj k K B hk hK X hX hXqs
  limitCone := (fgSubalgebraSystemLimitCone k K B hk hK X).cone
  isLimit := (fgSubalgebraSystemLimitCone k K B hk hK X).isLimit
  limitAlgebraicSpace := isAlgebraicSpace_fgSubalgebraSystemLimitCone_pt k K B hk hK X hX
  base := ⟨⊥, Subalgebra.fg_bot⟩

/-- The system of the descent situation is the system of base changes. -/
theorem fgSubalgebraDescentSituation_system (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXqc : IsQuasiCompactSpace B (Spec (.of k)) hk X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X) :
    (fgSubalgebraDescentSituation k K B hk hK X hX hXqc hXqs).system =
      fgSubalgebraSystem k K B hk hK X :=
  rfl

/-- The chosen limit cone of the descent situation is the chosen limit cone of the system. -/
theorem fgSubalgebraDescentSituation_limitCone (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXqc : IsQuasiCompactSpace B (Spec (.of k)) hk X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X) :
    (fgSubalgebraDescentSituation k K B hk hK X hX hXqc hXqs).limitCone =
      (fgSubalgebraSystemLimitCone k K B hk hK X).cone :=
  rfl

/-- The chosen index of the descent situation is the zero subalgebra. -/
theorem fgSubalgebraDescentSituation_base (hk : B.Contains (Spec (.of k)))
    (hK : B.Contains (Spec (.of K))) (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXqc : IsQuasiCompactSpace B (Spec (.of k)) hk X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X) :
    (fgSubalgebraDescentSituation k K B hk hK X hX hXqc hXqs).base =
      ⟨⊥, Subalgebra.fg_bot⟩ :=
  rfl

/-! ### Reading representability in and out of the situation -/

/-- **The restriction of a presheaf to the slice over `V` is representable as soon as its
product with the presheaf represented by `(V ⟶ U)` is.** A representing object of the product
comes with a morphism to `(V ⟶ U)`, and the object of the slice over `V` that morphism defines
represents the restriction. -/
theorem isRepresentable_relocalizeRestrict_of_isRepresentable_prod
    {C : Type (u + 1)} [Category.{u} C] {V U : C} (f : V ⟶ U) (F : (Over U)ᵒᵖ ⥤ Type u)
    (h : (FunctorToTypes.prod (yoneda.obj (Over.mk f)) F).IsRepresentable) :
    ((OverShriek.relocalizeRestrict f).obj F).IsRepresentable := by
  obtain ⟨R, ⟨e⟩⟩ := h.has_representation
  let p : R ⟶ Over.mk f := (e.homEquiv (𝟙 R)).1
  have hp {W : Over U} (g : W ⟶ R) : (e.homEquiv g).1 = g ≫ p := by
    have he' := congrArg Prod.fst (e.homEquiv_comp g (𝟙 R))
    change (e.homEquiv (g ≫ 𝟙 R)).1 = g ≫ p at he'
    simpa only [Category.comp_id] using he'
  let Y : Over V := Over.mk p.left
  let lift {W : Over V} (g : W ⟶ Y) : (Over.map f).obj W ⟶ R :=
    Over.homMk g.left (by
      show g.left ≫ R.hom = W.hom ≫ f
      rw [← p.w, ← Category.assoc]
      exact congrArg (fun t => t ≫ f) g.w)
  let canonical (W : Over V) : (Over.map f).obj W ⟶ Over.mk f := Over.homMk W.hom rfl
  have hfirst {W : Over V} (g : W ⟶ Y) : (e.homEquiv (lift g)).1 = canonical W := by
    rw [hp]
    exact Over.OverMorphism.ext g.w
  let inv {W : Over V} (x : F.obj (op ((Over.map f).obj W))) : W ⟶ Y :=
    Over.homMk (e.homEquiv.symm (canonical W, x)).left (by
      have hh := hp (e.homEquiv.symm (canonical W, x))
      have hh' := congrArg (fun t => t.1) (e.homEquiv.apply_symm_apply (canonical W, x))
      rw [hh'] at hh
      exact congrArg Over.Hom.left hh.symm)
  have hinv {W : Over V} (x : F.obj (op ((Over.map f).obj W))) :
      lift (inv x) = e.homEquiv.symm (canonical W, x) :=
    Over.OverMorphism.ext rfl
  refine ⟨Y, ⟨{ homEquiv := ?_, homEquiv_comp := ?_ }⟩⟩
  · intro W
    refine ⟨fun g => (e.homEquiv (lift g)).2, inv, ?_, ?_⟩
    · intro g
      apply Over.OverMorphism.ext
      show (e.homEquiv.symm (canonical W, (e.homEquiv (lift g)).2)).left = g.left
      rw [← hfirst g]
      exact congrArg Over.Hom.left (e.homEquiv.symm_apply_apply (lift g))
    · intro x
      show (e.homEquiv (lift (inv x))).2 = x
      rw [hinv]
      exact congrArg (fun t => t.2) (e.homEquiv.apply_symm_apply (canonical W, x))
  · intro W W' b g
    show (e.homEquiv (lift (b ≫ g))).2 = F.map ((Over.map f).map b).op _
    have hl : lift (b ≫ g) = (Over.map f).map b ≫ lift g := Over.OverMorphism.ext rfl
    rw [hl, e.homEquiv_comp]
    rfl

/-- **If a stage of the system is a scheme over `Spec k`, then `X_A` is a scheme over
`Spec A`.** The stage is the product of `X` with the presheaf represented by `Spec A`, and such
a product being representable makes the restriction of `X` to the site of `Spec A`
representable. This is how the conclusion of a descent statement applied to
`AlgebraicGeometry.Space.fgSubalgebraDescentSituation` is read back out. -/
theorem isRepresentable_relocalizeRestrict_of_isRepresentable_system_obj
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) (A : FGSubalgebra k K)
    (h : ((fgSubalgebraSystem k K B hk hK X).obj (op A)).IsRepresentable) :
    ((OverShriek.relocalizeRestrict (fgSubalgebraSiteHom k K B hk hK A)).obj
      X).IsRepresentable := by
  refine isRepresentable_relocalizeRestrict_of_isRepresentable_prod _ X ?_
  obtain ⟨W, ⟨r⟩⟩ := h.has_representation
  exact Functor.IsRepresentable.mk'
    (r.toIso ≪≫ (fgSubalgebraSystemObjIso k K B hk hK X A).symm ≪≫
      FunctorToTypes.binaryProductIso _ _)

/-- **If `X_K` is a scheme over `Spec K`, then the limit of the system is representable.** The
base change of `X` to `Spec K`, relocalized back to the site of `Spec k`, is the product of `X`
with the presheaf represented by `Spec K`, which is the limit of the system; the relocalization
of a representable presheaf is representable by [Stacks, Tag 03I4] part (2). This is the
hypothesis a descent statement applied to
`AlgebraicGeometry.Space.fgSubalgebraDescentSituation` has to be fed. -/
theorem isRepresentable_limitCone_pt_of_isRepresentable_relocalizeRestrict
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hXK : ((OverShriek.relocalizeRestrict (specExtensionHom k K B hk hK)).obj
      X).IsRepresentable) :
    ((fgSubalgebraSystemLimitCone k K B hk hK X).cone.pt).IsRepresentable := by
  obtain ⟨U, ⟨r⟩⟩ := hXK.has_representation
  exact Functor.IsRepresentable.mk'
    ((relocalizedYonedaRepresentableBy B (B.obj hK) (B.obj hk)
          (specExtensionHom k K B hk hK) U).toIso ≪≫
      (OverShriek.relocalizePresheafFunctor (specExtensionHom k K B hk hK)).mapIso r.toIso ≪≫
      OverShriek.relocalizeRestrictIsoProduct (specExtensionHom k K B hk hK) X ≪≫
      extensionBaseChangeIsoLimitConePt k K B hk hK X)


/-! ### A finitely generated stage which is a scheme -/

/-- **If `X_K` is a scheme then so is `X_A` for a finitely generated `k`-subalgebra `A` of `K`.**
This is the first half of the proof of [Stacks, Tag 0B84] part (2), with no condition on the
site.

The finitely generated subalgebras of `K` may be as many as the cofinality of the size cutoff of
the site, which [Stacks, Tag 07SR] does not allow. So the site is first enlarged to one whose
cutoff has larger cofinality (`AlgebraicGeometry.BigFppfSite.exists_isContained_lt_cof`); the
inverse image `X'` of `X` there is again a quasi-compact and quasi-separated algebraic space, and
`X'_K` is a scheme, because representability of a product with a represented sheaf is unchanged
by the enlargement (`AlgebraicGeometry.isRepresentable_prod_yoneda_iff_changeBigSite`). On the
enlarged site
[Stacks, Tag 07SR] applies to the descent situation of `X'`
(`AlgebraicGeometry.Space.fgSubalgebraDescentSituation`), and the stage `X'_A` it produces is a
scheme, hence so is `X_A`, by the same transport read backwards. -/
theorem exists_fgSubalgebra_isRepresentable_relocalizeRestrict
    (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXqc : IsQuasiCompactSpace B (Spec (.of k)) hk X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X)
    (hXK : ((OverShriek.relocalizeRestrict (specExtensionHom k K B hk hK)).obj
      X).IsRepresentable) :
    ∃ A : FGSubalgebra k K,
      ((OverShriek.relocalizeRestrict (fgSubalgebraSiteHom k K B hk hK A)).obj
        X).IsRepresentable := by
  obtain ⟨B', h, hcof⟩ := BigFppfSite.exists_isContained_lt_cof B
    (Cardinal.mk (FGSubalgebra k K))
  let Xs : AlgebraicSpaces B (Spec (.of k)) hk := ⟨X, hX⟩
  let hk' : B'.Contains (Spec (.of k)) := largerContains h hk
  let hK' : B'.Contains (Spec (.of K)) := largerContains h hK
  let X' := ((changeBigSite B B' h (Spec (.of k)) hk).obj Xs).obj
  have hX' : IsAlgebraicSpace B' (Spec (.of k)) hk' X' :=
    ((changeBigSite B B' h (Spec (.of k)) hk).obj Xs).property
  have hX'qc : IsQuasiCompactSpace B' (Spec (.of k)) hk' X' :=
    changeBigSite_isQuasiCompactSpace B B' h (Spec (.of k)) hk Xs hXqc
  have hX'qs : IsAbsolutelyQuasiSeparated B' (Spec (.of k)) hk' B'.contains_terminal X' :=
    changeBigSite_isAbsolutelyQuasiSeparated B B' h (Spec (.of k)) hk Xs hXqc hXqs
  -- `X ⨯ h_T` is an algebraic space for every object `T` of the site
  have hXT (T : BigFppfOver B (Spec (.of k)) hk) :
      IsAlgebraicSpace B (Spec (.of k)) hk (X ⨯ yoneda.obj T) :=
    (isAlgebraicSpace_pullback_yoneda_map_from k B hk X hX T).of_iso
      ((isPullback_prod_fst_snd_yoneda_obj T X).isoPullback.symm ≪≫ prod.braiding _ _)
  -- `X'_K` is a scheme on the enlarged site
  have hK2 : (X ⨯ yoneda.obj (specExtension k K B hk hK)).IsRepresentable :=
    @isRepresentable_of_natIso _ _ _ _
      ((extensionBaseChangeIsoLimitConePt k K B hk hK X).symm ≪≫ prod.braiding _ _)
      (isRepresentable_limitCone_pt_of_isRepresentable_relocalizeRestrict k K B hk hK X hXK)
  have hK3 := (isRepresentable_prod_yoneda_iff_changeBigSite B B' h (Spec (.of k)) hk Xs
    (specExtension k K B hk hK) (hXT _)).2 hK2
  have hlim : ((fgSubalgebraSystemLimitCone k K B' hk' hK' X').cone.pt).IsRepresentable :=
    @isRepresentable_of_natIso _ _ _ _
      (prod.braiding _ _ ≪≫ extensionBaseChangeIsoLimitConePt k K B' hk' hK' X') hK3
  -- a stage of the enlarged system is a scheme
  obtain ⟨A, hA⟩ := DescentSituation.exists_isRepresentable_system_obj_of_mk_lt
    (fgSubalgebraDescentSituation k K B' hk' hK' X' hX' hX'qc hX'qs) hcof hlim
  have hA1 : (X' ⨯ yoneda.obj ((inclusionOver h (Spec (.of k)) hk).obj
      (fgSubalgebraSiteObj k K B hk hK A))).IsRepresentable :=
    @isRepresentable_of_natIso _ _ _ _
      ((fgSubalgebraSystemObjIso k K B' hk' hK' X' A).symm ≪≫ prod.braiding _ _) hA
  -- read it back on the original site
  have hA2 := (isRepresentable_prod_yoneda_iff_changeBigSite B B' h (Spec (.of k)) hk Xs
    (fgSubalgebraSiteObj k K B hk hK A) (hXT _)).1 hA1
  exact ⟨A, isRepresentable_relocalizeRestrict_of_isRepresentable_system_obj k K B hk hK X A
    (@isRepresentable_of_natIso _ _ _ _
      (prod.braiding _ _ ≪≫ fgSubalgebraSystemObjIso k K B hk hK X A) hA2)⟩

end AlgebraicGeometry.Space

end
