module

public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.FunctorDescent
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ExplicitRestrictionSquare

/-!
# The descent datum assembled from the local functors of Gabriel–Rosenberg reconstruction

Let `X` and `Y` be quasi-compact and quasi-separated schemes and let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence.  Step 6 of [Stacks, Tag 0GPJ] produces, for a
quasi-compact open `U ⊆ X` and an open `V ⊆ Y` whose closed complements are matched by `e`, an
equivalence `QCoh(𝒪_U) ≌ QCoh(𝒪_V)`; combined with restriction to `U` this gives a functor
`QCoh(𝒪_X) ⥤ QCoh(𝒪_V)` for each such pair.  Step 3 then has to glue the functors obtained from
a *family* of such pairs into a single functor out of `QCoh(𝒪_X)` over `Y`.

This file assembles the descent datum that
`Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData` consumes, for a family of pairs
`(U i, V i)`.  The `i`-th local functor is

`M ↦ (e (((U i).ι)_* (M|_{U i})))|_{V i}`,

that is: the explicit bottom functor `AlgebraicGeometry.restrictionSquareFunctor` of step 6
precomposed with restriction to `U i`, read as a sheaf of `𝒪_{V i}`-modules.  The comparison over
an open `W` of `Y` contained in `V i` and in `V j` is

`(η j)|_W ∘ ((η i)|_W)⁻¹`,  where  `η i := e ((quasicoherentRestrictionUnit (U i).ι).app M)`,

both factors being invertible on the sections over `W` by
`AlgebraicGeometry.isIso_app_map_unit_of_le`.  Because every leg is built from the *same* module
`e M` by one of these maps, the cocycle condition telescopes.

## Main definitions

* `AlgebraicGeometry.ReconstructionGlue.appLinearEquiv` — a morphism of sheaves of modules which
  is invertible on the sections over one open, read as a linear equivalence there.
* `AlgebraicGeometry.ReconstructionGlue.transOf` — for two morphisms out of a common source, each
  invertible on the sections over one open, the transition from the first target to the second.
* `AlgebraicGeometry.ReconstructionGlue.extendFunctor` and `.extendModules` — the functor
  `M ↦ e (((U i).ι)_* (M|_{U i}))`, in the quasi-coherent and in the `Scheme.Modules` spelling.
* `AlgebraicGeometry.ReconstructionGlue.chartFunctor` — the `i`-th local functor
  `QCoh(𝒪_X) ⥤ (V i).Modules`.
* `AlgebraicGeometry.ReconstructionGlue.extendUnit`, `.chartUnit` and `.chartCompare` — the two
  factors of the comparison morphism `e M ⟶ ((V i).ι)_* ((chartFunctor i).obj M)` and their
  composite.
* `AlgebraicGeometry.ReconstructionGlue.glueData` — **the descent datum**, a
  `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData`.
* `AlgebraicGeometry.ReconstructionGlue.gluedFunctor`, `.gluedRestrictIso` and
  `.gluedQuasicoherentFunctor` — the glued functor, its comparison with the local functors, and
  its quasi-coherent form when the charts are affine.

## Main results

* `AlgebraicGeometry.ReconstructionGlue.transOf_app`, `.transOf_res`, `.transOf_trans` and
  `.transOf_congr` — the four conditions a `FunctorGlueData` asks of its comparison
  isomorphisms, proved once and for all for `AlgebraicGeometry.ReconstructionGlue.transOf`:
  compatibility with the comparison for one chart, with restriction, the cocycle condition, and
  compatibility with a morphism of the source category.
* `AlgebraicGeometry.ReconstructionGlue.isIso_restrictAdjunctionUnit_app` — the unit of the
  restriction–pushforward adjunction is invertible on the sections over an open contained in the
  image of the open immersion.
* `AlgebraicGeometry.ReconstructionGlue.isIso_chartCompare_app` — the comparison morphism is
  invertible on the sections over an open contained in `V i`.  This is where
  `AlgebraicGeometry.isIso_app_map_unit_of_le` enters.
* `AlgebraicGeometry.ReconstructionGlue.chartCompare_naturality` — the comparison morphism is
  natural in `M`.
* `AlgebraicGeometry.ReconstructionGlue.extendUnit_app`, `.chartUnit_app` and
  `.chartCompare_app_apply` — the comparison morphism on sections, in terms of the section data
  of `e` and one restriction map of the ambient scheme.
* `AlgebraicGeometry.ReconstructionGlue.glueData_trans_chartCompare` — the transition of the
  descent datum carries the `i`-th comparison to the `j`-th one, which is the inverse-free form
  of `(η j)|_W ∘ ((η i)|_W)⁻¹`.
* `AlgebraicGeometry.ReconstructionGlue.chartFunctor_obj` and
  `.isQuasicoherent_chartFunctor_obj` — the `i`-th local functor is
  `AlgebraicGeometry.restrictionSquareFunctor` precomposed with restriction to `U i`, and it
  takes quasi-coherent values.

## Implementation notes

**Transitions are indexed by opens of the ambient scheme.**  A transition is indexed by an open `W`
of the *ambient* scheme `Y` together with two containments `W ≤ V i` and `W ≤ V j`, never by an
open of `V i ⊓ V j`; both its source and its target are modules over `𝒪_Y(W)`, so no transport
appears.  The cocycle condition is then literally the telescoping of
`chartCompare j ∘ (chartCompare i)⁻¹` with `chartCompare k ∘ (chartCompare j)⁻¹`, which is
`AlgebraicGeometry.ReconstructionGlue.transOf_trans`, one application of
`LinearEquiv.symm_apply_apply`.

**Why the comparison has two factors.**  The sections of `((V i).ι)_* ((chartFunctor i).obj M)`
over `W` are by definition the sections of `e (((U i).ι)_* (M|_{U i}))` over
`(V i).ι ''ᵁ ((V i).ι ⁻¹ᵁ W)`, an open *equal* to `W` but not definitionally so.  The second
factor `AlgebraicGeometry.ReconstructionGlue.chartUnit` is exactly the restriction map between
those two opens: it is the unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` for
`(V i).ι`, whose formula on sections is that restriction map, and it is invertible over
`W ≤ V i` because then the two opens agree.  Putting the identification inside the comparison
rather than beside it is what keeps the datum free of `eqToHom`.

**No `rw` on composites of these types.**  `AlgebraicGeometry.Scheme.Modules.restrictFunctor` is
not reducible, so a composite whose type mentions it is not type-correct at the `implicit`
transparency level and `rw [Category.assoc]` on it fails.  Every reassociation below is
therefore done in term mode, with `CategoryTheory.Category.assoc` and `congrArg`, and every
elementwise step goes through `AlgebraicGeometry.ReconstructionGlue.square_app_apply`.

**One spelling of the module category.**  The category of quasi-coherent modules is a full
subcategory of `SheafOfModules Y.ringCatSheaf`, while the descent machinery is stated for
`AlgebraicGeometry.Scheme.Modules`.  The two are the same category but not reducibly so, and
field notation resolves against the head symbol of a type, so the crossing is confined to
`AlgebraicGeometry.qcohUnderlying` and `AlgebraicGeometry.qcohUnderlyingHom`:
`AlgebraicGeometry.ReconstructionGlue.extendModules` is a hand-built functor whose object and
morphism assignments are those two abbreviations applied to
`AlgebraicGeometry.ReconstructionGlue.extendFunctor`, rather than a composite with
`CategoryTheory.ObjectProperty.ι`.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules
open Stacks.AlgebraicGeometry.ModuleFunctorDescent

universe u

namespace AlgebraicGeometry.ReconstructionGlue

/-! ### Linear equivalences from invertibility on one open -/

section Sections

variable {S : Scheme.{u}}

/-- **A commuting square of morphisms of sheaves of modules, read on the sections over one
open.**  Both `AlgebraicGeometry.Scheme.Modules.Hom.comp_app` and
`CategoryTheory.ConcreteCategory.comp_apply` are needed to turn the square into a statement about
nested applications; this packages the two. -/
theorem square_app_apply {M N M' N' : S.Modules} {φ : M ⟶ N} {β : N ⟶ N'} {α : M ⟶ M'}
    {φ' : M' ⟶ N'} (h : φ ≫ β = α ≫ φ') (W : S.Opens) (s : Γ(M, W)) :
    β.app W (φ.app W s) = φ'.app W (α.app W s) := by
  have h2 := congr($(congrArg (fun k => Scheme.Modules.Hom.app k W) h) s)
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h2

/-- **A morphism of sheaves of modules which is invertible on the sections over one open, read
as a linear equivalence there.**  The invertibility is an explicit argument rather than an
instance because the comparison morphisms below are invertible only over the opens contained in
a chart, so it is always supplied by hand; `IsIso` is a `Prop`, so which proof is supplied never
matters. -/
def appLinearEquiv {M N : S.Modules} (φ : M ⟶ N) (W : S.Opens) (h : IsIso (φ.app W)) :
    M.val.obj (op W) ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op W))] N.val.obj (op W) :=
  haveI := h
  haveI : IsIso ((forget₂ (ModuleCat (ToType (S.ringCatSheaf.obj.obj (op W)))) AddCommGrpCat).map
      (φ.val.app (op W))) := inferInstanceAs (IsIso (φ.app W))
  haveI : IsIso (φ.val.app (op W)) :=
    isIso_of_reflects_iso (φ.val.app (op W)) (forget₂ (ModuleCat _) AddCommGrpCat)
  (asIso (φ.val.app (op W))).toLinearEquiv

/-- `AlgebraicGeometry.ReconstructionGlue.appLinearEquiv` acts on sections as the morphism
does. -/
@[simp] theorem appLinearEquiv_apply {M N : S.Modules} (φ : M ⟶ N) (W : S.Opens)
    (h : IsIso (φ.app W)) (s : Γ(M, W)) : appLinearEquiv φ W h s = φ.app W s :=
  rfl

/-- **The linear equivalence commutes with the restriction maps**, because the morphism it comes
from does. -/
theorem appLinearEquiv_res {M N : S.Modules} (φ : M ⟶ N) {W W' : S.Opens} (hW : W' ≤ W)
    (h : IsIso (φ.app W)) (h' : IsIso (φ.app W')) (s : Γ(M, W)) :
    appLinearEquiv φ W' h' (M.presheaf.map (homOfLE hW).op s)
      = N.presheaf.map (homOfLE hW).op (appLinearEquiv φ W h s) :=
  (Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map φ hW s).symm

/-- **The inverse linear equivalence commutes with the restriction maps.** -/
theorem appLinearEquiv_symm_res {M N : S.Modules} (φ : M ⟶ N) {W W' : S.Opens} (hW : W' ≤ W)
    (h : IsIso (φ.app W)) (h' : IsIso (φ.app W')) (t : Γ(N, W)) :
    (appLinearEquiv φ W' h').symm (N.presheaf.map (homOfLE hW).op t)
      = M.presheaf.map (homOfLE hW).op ((appLinearEquiv φ W h).symm t) :=
  (appLinearEquiv φ W' h').injective
    (((appLinearEquiv φ W' h').apply_symm_apply _).trans
      (((appLinearEquiv_res φ hW h h' ((appLinearEquiv φ W h).symm t)).trans
        (congrArg (fun x => N.presheaf.map (homOfLE hW).op x)
          ((appLinearEquiv φ W h).apply_symm_apply t))).symm))

/-- **The transition between the two targets of a pair of morphisms out of a common source**,
each invertible on the sections over the open `W`: invert the first, then apply the second.  This
is the shape of every comparison isomorphism of the descent datum below, and the four lemmas that
follow are the four conditions a
`Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData` asks of them. -/
def transOf {E M N : S.Modules} (φ : E ⟶ M) (ψ : E ⟶ N) (W : S.Opens)
    (hφ : IsIso (φ.app W)) (hψ : IsIso (ψ.app W)) :
    M.val.obj (op W) ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op W))] N.val.obj (op W) :=
  (appLinearEquiv φ W hφ).symm.trans (appLinearEquiv ψ W hψ)

/-- **The transition carries the first comparison to the second.** -/
theorem transOf_app {E M N : S.Modules} (φ : E ⟶ M) (ψ : E ⟶ N) (W : S.Opens)
    (hφ : IsIso (φ.app W)) (hψ : IsIso (ψ.app W)) (t : Γ(E, W)) :
    transOf φ ψ W hφ hψ (φ.app W t) = ψ.app W t :=
  congrArg (appLinearEquiv ψ W hψ) ((appLinearEquiv φ W hφ).symm_apply_apply t)

/-- **The transition commutes with the restriction maps.** -/
theorem transOf_res {E M N : S.Modules} (φ : E ⟶ M) (ψ : E ⟶ N) {W W' : S.Opens} (hW : W' ≤ W)
    (hφ : IsIso (φ.app W)) (hψ : IsIso (ψ.app W)) (hφ' : IsIso (φ.app W'))
    (hψ' : IsIso (ψ.app W')) (s : Γ(M, W)) :
    transOf φ ψ W' hφ' hψ' (M.presheaf.map (homOfLE hW).op s)
      = N.presheaf.map (homOfLE hW).op (transOf φ ψ W hφ hψ s) :=
  (congrArg (appLinearEquiv ψ W' hψ') (appLinearEquiv_symm_res φ hW hφ hφ' s)).trans
    (appLinearEquiv_res ψ hW hψ hψ' ((appLinearEquiv φ W hφ).symm s))

/-- **The cocycle condition**: the transitions out of a common source telescope. -/
theorem transOf_trans {E M N P : S.Modules} (φ : E ⟶ M) (ψ : E ⟶ N) (χ : E ⟶ P) (W : S.Opens)
    (hφ : IsIso (φ.app W)) (hψ : IsIso (ψ.app W)) (hχ : IsIso (χ.app W)) (s : Γ(M, W)) :
    transOf ψ χ W hψ hχ (transOf φ ψ W hφ hψ s) = transOf φ χ W hφ hχ s :=
  transOf_app ψ χ W hψ hχ ((appLinearEquiv φ W hφ).symm s)

/-- **The transitions are compatible with a morphism of the ambient data.**  Given two
commuting squares with the same left edge `α`, the transitions at the two ends agree. -/
theorem transOf_congr {E M N E' M' N' : S.Modules} (φ : E ⟶ M) (ψ : E ⟶ N) (φ' : E' ⟶ M')
    (ψ' : E' ⟶ N') (α : E ⟶ E') (β : M ⟶ M') (γ : N ⟶ N') (W : S.Opens)
    (hφ : IsIso (φ.app W)) (hψ : IsIso (ψ.app W)) (hφ' : IsIso (φ'.app W))
    (hψ' : IsIso (ψ'.app W)) (hβ : φ ≫ β = α ≫ φ') (hγ : ψ ≫ γ = α ≫ ψ') (s : Γ(M, W)) :
    transOf φ' ψ' W hφ' hψ' (β.app W s) = γ.app W (transOf φ ψ W hφ hψ s) :=
  have hs : φ.app W ((appLinearEquiv φ W hφ).symm s) = s :=
    (appLinearEquiv φ W hφ).apply_symm_apply s
  (congrArg (fun x => transOf φ' ψ' W hφ' hψ' (β.app W x)) hs.symm).trans
    ((congrArg (transOf φ' ψ' W hφ' hψ') (square_app_apply hβ W _)).trans
      ((transOf_app φ' ψ' W hφ' hψ' (α.app W ((appLinearEquiv φ W hφ).symm s))).trans
        (square_app_apply hγ W ((appLinearEquiv φ W hφ).symm s)).symm))

/-- **The unit of the restriction–pushforward adjunction is invertible on the sections over an
open contained in the image of the open immersion.**  On sections the unit is the restriction map
from `W` to `j (j⁻¹ W)` (`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`), and
for `W` inside the image of `j` those two opens are equal, so the map is the image under the
presheaf of an `eqToHom`. -/
theorem isIso_restrictAdjunctionUnit_app {Z : Scheme.{u}} (j : Z ⟶ S) [IsOpenImmersion j]
    (N : S.Modules) (W : S.Opens) (hW : W ≤ j.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction j).unit.app N).app W) := by
  have hWeq : j ''ᵁ (j ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have h2 : homOfLE (j.image_preimage_le W) = eqToHom hWeq := rfl
  rw [h2, eqToHom_op]
  exact CategoryTheory.Functor.map_isIso _ _

end Sections

/-! ### The local functors and the comparison morphism -/

section Charts

variable {X Y : Scheme.{u}} [QuasiSeparatedSpace X]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
  {ι : Type u} (U : ι → X.Opens) [∀ i, CompactSpace (U i).toScheme] (V : ι → Y.Opens)

/-- **The `i`-th extension functor**, `M ↦ e (((U i).ι)_* (M|_{U i}))`: restrict to the
quasi-compact open `U i`, extend back to `X` by pushing forward along the open immersion, and
apply `e`. -/
def extendFunctor (i : ι) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
  quasicoherentRestriction (U i).ι ⋙ quasicoherentPushforward (U i).ι ⋙ e.functor

/-- **The `i`-th extension functor, valued in `𝒪_Y`-modules.**  This is
`AlgebraicGeometry.ReconstructionGlue.extendFunctor` read through
`AlgebraicGeometry.qcohUnderlying`; it is built by hand rather than as a composite with
`CategoryTheory.ObjectProperty.ι` so that its stated type uses the
`AlgebraicGeometry.Scheme.Modules` spelling, on which the section-level interface resolves. -/
def extendModules (i : ι) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ Y.Modules where
  obj M := qcohUnderlying ((extendFunctor e U i).obj M)
  map φ := qcohUnderlyingHom ((extendFunctor e U i).map φ)
  map_id M := by rw [CategoryTheory.Functor.map_id]; rfl
  map_comp φ ψ := by rw [CategoryTheory.Functor.map_comp]; rfl

/-- **The `i`-th local functor of step 3 of [Stacks, Tag 0GPJ]**, the restriction of
`AlgebraicGeometry.ReconstructionGlue.extendModules` to the chart `V i`.  Up to the comparison
isomorphism `AlgebraicGeometry.restrictionSquareIso` this is restriction to `U i` followed by the
explicit bottom functor `AlgebraicGeometry.restrictionSquareFunctor` of step 6. -/
def chartFunctor (i : ι) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ (V i).toScheme.Modules :=
  extendModules e U i ⋙ Scheme.Modules.restrictFunctor (V i).ι

/-- **`e` applied to the unit of the extension along `U i`**, as a morphism of `𝒪_Y`-modules.
This is the first factor of the comparison, and the one that
`AlgebraicGeometry.isIso_app_map_unit_of_le` inverts over the opens contained in `V i`. -/
def extendUnit (i : ι)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    qcohUnderlying (e.functor.obj M) ⟶ (extendModules e U i).obj M :=
  qcohUnderlyingHom (e.functor.map ((quasicoherentRestrictionUnit (U i).ι).app M))

/-- **The unit of the restriction–pushforward adjunction for the chart `V i`**, the second factor
of the comparison.  On sections over `W` it is the restriction map from `W` to
`(V i).ι ((V i).ι⁻¹ W)`, which is the identification the descent datum would otherwise have to
carry as an `eqToHom`. -/
def chartUnit (i : ι)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (extendModules e U i).obj M ⟶ push ((V i).ι) ((chartFunctor e U V i).obj M) :=
  (Scheme.Modules.restrictAdjunction (V i).ι).unit.app ((extendModules e U i).obj M)

/-- **The comparison morphism of the `i`-th chart**,
`e M ⟶ ((V i).ι)_* ((chartFunctor i).obj M)`: `e` of the unit of the extension along `U i`,
followed by the unit of the restriction–pushforward adjunction for `(V i).ι`. -/
def chartCompare (i : ι)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    qcohUnderlying (e.functor.obj M) ⟶ push ((V i).ι) ((chartFunctor e U V i).obj M) :=
  extendUnit e U i M ≫ chartUnit e U V i M

/-- The two factors of `AlgebraicGeometry.ReconstructionGlue.chartCompare`, on sections. -/
theorem chartCompare_app (i : ι)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (W : Y.Opens) :
    (chartCompare e U V i M).app W
      = (extendUnit e U i M).app W ≫ (chartUnit e U V i M).app W :=
  rfl

/-- **The first factor of the comparison, on sections**: it is `e` applied to the unit
`M ⟶ ((U i).ι)_* (M|_{U i})`, read on the sections over `W`. -/
theorem extendUnit_app (i : ι)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (W : Y.Opens) :
    (extendUnit e U i M).app W
      = (qcohUnderlyingHom
          (e.functor.map ((quasicoherentRestrictionUnit (U i).ι).app M))).app W :=
  rfl

/-- **The second factor of the comparison, on sections**: it is the restriction map of
`e (((U i).ι)_* (M|_{U i}))` from `W` to the open `(V i).ι ((V i).ι⁻¹ W)` contained in it.  For
`W ≤ V i` the two opens are equal, which is why this factor is then invertible. -/
theorem chartUnit_app (i : ι)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (W : Y.Opens) :
    (chartUnit e U V i M).app W
      = ((extendModules e U i).obj M).presheaf.map
          (homOfLE ((V i).ι.image_preimage_le W)).op :=
  rfl

/-- **The comparison morphism on sections**, as the composite of its two factors. -/
theorem chartCompare_app_apply (i : ι)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (W : Y.Opens)
    (t : Γ(qcohUnderlying (e.functor.obj M), W)) :
    (chartCompare e U V i M).app W t
      = (chartUnit e U V i M).app W ((extendUnit e U i M).app W t) := by
  simp only [chartCompare_app, ConcreteCategory.comp_apply]

/-- **The first factor of the comparison is natural in `M`**, because
`AlgebraicGeometry.quasicoherentRestrictionUnit` is a natural transformation and `e` is a
functor. -/
theorem extendUnit_naturality (i : ι)
    {M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    qcohUnderlyingHom (e.functor.map φ) ≫ extendUnit e U i N
      = extendUnit e U i M ≫ (extendModules e U i).map φ :=
  have h1 : e.functor.map φ ≫ e.functor.map ((quasicoherentRestrictionUnit (U i).ι).app N)
      = e.functor.map ((quasicoherentRestrictionUnit (U i).ι).app M) ≫
        e.functor.map ((quasicoherentRestriction (U i).ι ⋙
          quasicoherentPushforward (U i).ι).map φ) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg e.functor.map ((quasicoherentRestrictionUnit (U i).ι).naturality φ)
  congrArg (fun f => qcohUnderlyingHom f) h1

/-- **The second factor of the comparison is natural in `M`**, being the unit of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. -/
theorem chartUnit_naturality (i : ι)
    {M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    (extendModules e U i).map φ ≫ chartUnit e U V i N
      = chartUnit e U V i M ≫ pushHom ((V i).ι) ((chartFunctor e U V i).map φ) :=
  (Scheme.Modules.restrictAdjunction (V i).ι).unit.naturality ((extendModules e U i).map φ)

/-- **The comparison morphism is natural in `M`.**  The reassociation is done in term mode:
the type of the composite mentions `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which is
not reducible, so `rw [Category.assoc]` is not available here. -/
theorem chartCompare_naturality (i : ι)
    {M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    qcohUnderlyingHom (e.functor.map φ) ≫ chartCompare e U V i N
      = chartCompare e U V i M ≫ pushHom ((V i).ι) ((chartFunctor e U V i).map φ) :=
  calc qcohUnderlyingHom (e.functor.map φ) ≫ chartCompare e U V i N
      = (qcohUnderlyingHom (e.functor.map φ) ≫ extendUnit e U i N) ≫ chartUnit e U V i N :=
        (Category.assoc _ _ _).symm
    _ = (extendUnit e U i M ≫ (extendModules e U i).map φ) ≫ chartUnit e U V i N :=
        congrArg (fun k => k ≫ chartUnit e U V i N) (extendUnit_naturality e U i φ)
    _ = extendUnit e U i M ≫ ((extendModules e U i).map φ ≫ chartUnit e U V i N) :=
        Category.assoc _ _ _
    _ = extendUnit e U i M ≫
          (chartUnit e U V i M ≫ pushHom ((V i).ι) ((chartFunctor e U V i).map φ)) :=
        congrArg (fun k => extendUnit e U i M ≫ k) (chartUnit_naturality e U V i φ)
    _ = chartCompare e U V i M ≫ pushHom ((V i).ι) ((chartFunctor e U V i).map φ) :=
        (Category.assoc _ _ _).symm

/-- **The `i`-th local functor is the explicit bottom functor of step 6 of [Stacks, Tag 0GPJ]
precomposed with restriction to `U i`**, on objects.  This is what makes
`AlgebraicGeometry.ReconstructionGlue.chartFunctor` the functor step 3 is supposed to glue:
`AlgebraicGeometry.restrictionSquareFunctor` is the bottom functor, and
`AlgebraicGeometry.restrictionSquareIso` compares the composite with `e` followed by restriction
to `V i`. -/
theorem chartFunctor_obj (i : ι)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (chartFunctor e U V i).obj M
      = qcohUnderlying ((restrictionSquareFunctor e (U i) (V i)).obj
          ((quasicoherentRestriction (U i).ι).obj M)) :=
  rfl

/-- **The local functors take quasi-coherent values**, being restrictions of quasi-coherent
modules; this is what discharges the quasi-coherence hypothesis of the glued functor. -/
theorem isQuasicoherent_chartFunctor_obj (i : ι)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((chartFunctor e U V i).obj M).IsQuasicoherent :=
  ((quasicoherentRestriction (V i).ι).obj ((extendFunctor e U i).obj M)).property

end Charts

/-! ### The descent datum -/

section GlueData

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
  {ι : Type u} (U : ι → X.Opens) [∀ i, CompactSpace (U i).toScheme] (V : ι → Y.Opens)
  (Z : ι → Set X) (T : ι → Set Y)
  (hcorr : ∀ (i : ι) (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory),
    quasicoherentSupportedOn X (Z i) E ↔ quasicoherentSupportedOn Y (T i) (e.functor.obj E))
  (hUZ : ∀ i, (U i : Set X) = (Z i)ᶜ) (hVT : ∀ i, (V i : Set Y) = (T i)ᶜ)
  (hV : ∀ i, IsCompact (V i : Set Y))

include hcorr hUZ hVT hV

/-- **The comparison morphism of the `i`-th chart is invertible on the sections over an open
contained in `V i`.**  The first factor is invertible by
`AlgebraicGeometry.isIso_app_map_unit_of_le` — the independence of the extension, which is the
substance of step 6 of [Stacks, Tag 0GPJ] — and the second by
`AlgebraicGeometry.ReconstructionGlue.isIso_restrictAdjunctionUnit_app`. -/
theorem isIso_chartCompare_app (i : ι)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (W : Y.Opens)
    (hW : W ≤ V i) : IsIso ((chartCompare e U V i M).app W) := by
  have h1 : IsIso ((extendUnit e U i M).app W) :=
    isIso_app_map_unit_of_le e (U i) (V i) (Z i) (T i) (hcorr i) (hUZ i) (hVT i) (hV i) M W hW
  have h2 : IsIso ((chartUnit e U V i M).app W) :=
    isIso_restrictAdjunctionUnit_app (V i).ι ((extendModules e U i).obj M) W
      (le_of_le_of_eq hW ((V i).opensRange_ι).symm)
  rw [chartCompare_app]
  exact IsIso.comp_isIso

/-- `AlgebraicGeometry.ReconstructionGlue.isIso_chartCompare_app` with the containment phrased
for the image of the chart inclusion, which is the form the descent datum supplies. -/
theorem chartIsIso (i : ι)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (W : Y.Opens)
    (hW : W ≤ ((V i).ι).opensRange) : IsIso ((chartCompare e U V i M).app W) :=
  isIso_chartCompare_app e U V Z T hcorr hUZ hVT hV i M W
    (le_of_le_of_eq hW ((V i).opensRange_ι))

/-- **The descent datum of the local functors of step 3 of [Stacks, Tag 0GPJ].**  The `i`-th
functor is `AlgebraicGeometry.ReconstructionGlue.chartFunctor`, and the transition over an open
`W` of `Y` contained in both chart images is
`AlgebraicGeometry.ReconstructionGlue.transOf` applied to the two comparison morphisms
`AlgebraicGeometry.ReconstructionGlue.chartCompare`, which share the source `e M`.  Sharing the
source is what makes the cocycle condition telescope. -/
def glueData :
    FunctorGlueData Y (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory
      (fun i => (V i).ι) where
  functor i := chartFunctor e U V i
  trans := fun i j {W} hi hj M =>
    transOf (chartCompare e U V i M) (chartCompare e U V j M) W
      (chartIsIso e U V Z T hcorr hUZ hVT hV i M W hi)
      (chartIsIso e U V Z T hcorr hUZ hVT hV j M W hj)
  trans_map := fun i j {W W'} hi hj hW'W M s =>
    transOf_res (chartCompare e U V i M) (chartCompare e U V j M) hW'W
      (chartIsIso e U V Z T hcorr hUZ hVT hV i M W hi)
      (chartIsIso e U V Z T hcorr hUZ hVT hV j M W hj)
      (chartIsIso e U V Z T hcorr hUZ hVT hV i M W' (hW'W.trans hi))
      (chartIsIso e U V Z T hcorr hUZ hVT hV j M W' (hW'W.trans hj)) s
  trans_naturality := fun i j {W} hi hj {A B} φ s =>
    transOf_congr (chartCompare e U V i A) (chartCompare e U V j A)
      (chartCompare e U V i B) (chartCompare e U V j B)
      (qcohUnderlyingHom (e.functor.map φ)) (pushHom ((V i).ι) ((chartFunctor e U V i).map φ))
      (pushHom ((V j).ι) ((chartFunctor e U V j).map φ)) W
      (chartIsIso e U V Z T hcorr hUZ hVT hV i A W hi)
      (chartIsIso e U V Z T hcorr hUZ hVT hV j A W hj)
      (chartIsIso e U V Z T hcorr hUZ hVT hV i B W hi)
      (chartIsIso e U V Z T hcorr hUZ hVT hV j B W hj)
      (chartCompare_naturality e U V i φ).symm (chartCompare_naturality e U V j φ).symm s
  trans_trans := fun i j k {W} hi hj hk M s =>
    transOf_trans (chartCompare e U V i M) (chartCompare e U V j M) (chartCompare e U V k M) W
      (chartIsIso e U V Z T hcorr hUZ hVT hV i M W hi)
      (chartIsIso e U V Z T hcorr hUZ hVT hV j M W hj)
      (chartIsIso e U V Z T hcorr hUZ hVT hV k M W hk) s

/-- The `i`-th functor of the descent datum is the `i`-th local functor. -/
@[simp] theorem glueData_functor (i : ι) :
    (glueData e U V Z T hcorr hUZ hVT hV).functor i = chartFunctor e U V i :=
  rfl

/-- **The transition of the descent datum is the second comparison composed with the inverse of
the first.**  Stated in the form that does not mention the inverse: the transition carries the
`i`-th comparison of a section of `e M` to the `j`-th one.  Together with
`AlgebraicGeometry.ReconstructionGlue.chartCompare_app_apply`,
`AlgebraicGeometry.ReconstructionGlue.extendUnit_app` and
`AlgebraicGeometry.ReconstructionGlue.chartUnit_app` this describes the datum on sections
entirely in terms of the section data of `e`. -/
theorem glueData_trans_chartCompare (i j : ι) {W : Y.Opens}
    (hi : W ≤ ((V i).ι).opensRange) (hj : W ≤ ((V j).ι).opensRange)
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (t : Γ(qcohUnderlying (e.functor.obj M), W)) :
    (glueData e U V Z T hcorr hUZ hVT hV).trans i j hi hj M
        ((chartCompare e U V i M).app W t)
      = (chartCompare e U V j M).app W t :=
  transOf_app (chartCompare e U V i M) (chartCompare e U V j M) W
    (chartIsIso e U V Z T hcorr hUZ hVT hV i M W hi)
    (chartIsIso e U V Z T hcorr hUZ hVT hV j M W hj) t

/-- **The glued functor** `QCoh(𝒪_X) ⥤ 𝒪_Y`-modules, obtained from the descent datum by
Tag 00AM.  The covering hypothesis is taken as an argument: that the chart images cover `Y` is a
separate step of [Stacks, Tag 0GPJ]. -/
def gluedFunctor (hU : IsOpenCover fun i => ((V i).ι).opensRange) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ Y.Modules :=
  (glueData e U V Z T hcorr hUZ hVT hV).glued hU

/-- **The glued functor restricts along each chart to the local functor it was glued from.** -/
def gluedRestrictIso (hU : IsOpenCover fun i => ((V i).ι).opensRange) (i : ι) :
    gluedFunctor e U V Z T hcorr hUZ hVT hV hU ⋙ Scheme.Modules.restrictFunctor ((V i).ι)
      ≅ chartFunctor e U V i :=
  (glueData e U V Z T hcorr hUZ hVT hV).restrictIso hU i

/-- **The glued functor into the quasi-coherent modules, for affine charts.**  When the `V i`
are affine opens the glued sheaf of modules is quasi-coherent — quasi-coherence is local and a
quasi-coherent module on an affine scheme has a global presentation — so the glued functor
factors through `QCoh(𝒪_Y)`.  This is the shape step 3 of [Stacks, Tag 0GPJ] consumes. -/
def gluedQuasicoherentFunctor (hU : IsOpenCover fun i => ((V i).ι).opensRange)
    (hVaff : ∀ i, IsAffineOpen (V i)) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
  (glueData e U V Z T hcorr hUZ hVT hV).gluedQuasicoherentOfAffineOpen hU hVaff
    fun i M => isQuasicoherent_chartFunctor_obj e U V i M

/-- Composing the quasi-coherent form of the glued functor with the inclusion of the
quasi-coherent modules returns the glued functor, so
`AlgebraicGeometry.ReconstructionGlue.gluedRestrictIso` is its comparison too. -/
@[simp] theorem gluedQuasicoherentFunctor_comp_ι
    (hU : IsOpenCover fun i => ((V i).ι).opensRange) (hVaff : ∀ i, IsAffineOpen (V i)) :
    gluedQuasicoherentFunctor e U V Z T hcorr hUZ hVT hV hU hVaff ⋙
        (Stacks.AlgebraicGeometry.ModuleNatTransGlue.quasicoherent Y).ι
      = gluedFunctor e U V Z T hcorr hUZ hVT hV hU :=
  rfl

end GlueData

end AlgebraicGeometry.ReconstructionGlue

end
