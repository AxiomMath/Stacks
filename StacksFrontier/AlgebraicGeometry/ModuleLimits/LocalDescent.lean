module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictSections
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictCanHom

/-!
# The canonical equation of Tag 01ZR (2), localized to an open and read on sections

[Stacks Project, Tag 01ZR] (2) asks for a morphism at a stage whose pullback to the limit is the
given morphism *through the canonical identifications*.  Proving it for a quasi-compact
quasi-separated stage out of the affine case means checking that equation locally on an affine
open covering and then glueing, and for that the equation has to be available in a form which
(a) makes sense over an open of the stage only, and (b) restricts to a smaller open for free.

`Stacks.AlgebraicGeometry.ModuleLimits.LocalCanonicalEq` is that form.  It is the canonical
equation read on *pulled-back sections*: a morphism out of a pullback is determined by what it
does to them (`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_doublePullbackSection`), so no
information is lost, and the condition only ever mentions the local datum through its action on
sections — which is why restricting the open it is stated over costs nothing.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.valSections`: the action on sections of a morphism
  between the restrictions to an open, in the `· .val` spelling.
* `Stacks.AlgebraicGeometry.ModuleLimits.pullbackRestrictHom`: the pullback of such a morphism
  along a morphism of schemes, as a morphism between the restrictions of the pullbacks.
* `Stacks.AlgebraicGeometry.ModuleLimits.LocalCanonicalEq`,
  `Stacks.AlgebraicGeometry.ModuleLimits.LocalDescent`: the localized canonical equation, for a
  family of maps on sections resp. for a morphism of restrictions.
* `Stacks.AlgebraicGeometry.ModuleLimits.transportRestrictHom`: the transport of a local descent
  datum to a later stage.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.valSections_pullbackRestrictHom`: **the pullback of a
  morphism of restrictions, on a pulled-back section** — the computation that makes the whole
  localization work.
* `Stacks.AlgebraicGeometry.ModuleLimits.canonical_eq_of_localCanonicalEq`: a morphism whose
  action on sections satisfies the localized equation over the whole stage satisfies the
  canonical equation of the tag.
* `Stacks.AlgebraicGeometry.ModuleLimits.localDescent_restrictTo`: a local descent datum
  restricts to a smaller open.
* `Stacks.AlgebraicGeometry.ModuleLimits.localDescent_transport`: a local descent datum
  transports to a later stage, by
  `Stacks.AlgebraicGeometry.ModuleLimits.canHom_cocycle`.

## Implementation notes

Everything here is written in the `· .val.app (op U)` / `· .val.obj (op U)` spelling, because
that is the spelling of the `AlgebraicGeometry.Scheme.Modules.pullbackSection` API this file
computes with.  `valSections` is `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections`
rewritten in it, and `restrictSections_eq_valSections` is the one bridge; the `Γ(M, U)` spelling
is kept for the glueing interface, where the hypotheses are stated with `Γ(X, U)`-scalars.

Two shape points matter.  A rewrite whose pattern carries a metavariable in the
section argument **fails** on every goal here, because the composite of a morphism of
restrictions with an ambient section is type-correct only up to an unfolding unavailable at
reducible transparency; the cure is to instantiate the rewrite rule completely, and the
statements above are arranged so that this is always possible.  And the local datum is passed to
`LocalCanonicalEq` as `valSections Θ` rather than as `fun W hW => valSections Θ W hW`: the
`fun` leaves a beta-redex in the goal after `intro`, and no rewrite matches through it.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

section ValSections

variable {X : Scheme.{u}} {M N : X.Modules}

/-! ### The sectionwise family in the `· .val` spelling

The `AlgebraicGeometry.Scheme.Modules.pullbackSection` API is stated in the
`· .val.app (op U)` / `· .val.obj (op U)` spelling, and a statement that mixes it with the
`Γ(M, U)` spelling of the section modules is not type-correct at reducible transparency, so
`rw` fails on it.  `valSections` is `restrictSections` written entirely in the former spelling;
`restrictSections_eq_valSections` is the one bridge between them. -/

/-- The action on sections of a morphism of the restrictions to `O`, in the `· .val` spelling. -/
noncomputable def valSections {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U : X.Opens) (h : U ≤ O) (m : M.val.obj (op U)) : N.val.obj (op U) :=
  N.val.map (homOfLE (image_preimage_of_le h).ge).op
    (θ.val.app (op (O.ι ⁻¹ᵁ U)) (M.val.map (homOfLE (O.ι.image_preimage_le U)).op m))

/-- `restrictSections` agrees with `valSections`: the bridge between the `Γ(M, U)` spelling and
the `· .val` spelling of the sectionwise action. -/
theorem restrictSections_eq_valSections {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U : X.Opens) (h : U ≤ O) (m : M.val.obj (op U)) :
    restrictSections θ U h m = valSections θ U h m :=
  restrictSections_apply θ U h m

/-- `valSections` of a composite is the composite of the two actions on sections. -/
theorem valSections_comp {K : X.Modules} {O : X.Opens}
    (α : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (β : Scheme.Modules.restrict N O.ι ⟶ Scheme.Modules.restrict K O.ι)
    (U : X.Opens) (h : U ≤ O) (m : M.val.obj (op U)) :
    valSections (α ≫ β) U h m = valSections β U h (valSections α U h m) := by
  unfold valSections
  rw [comp_val_app α β (O.ι ⁻¹ᵁ U)
      (M.val.map (homOfLE (O.ι.image_preimage_le U)).op m),
    val_map_homOfLE_self (M := N) (image_preimage_of_le h).ge (O.ι.image_preimage_le U)
      (α.val.app (op (O.ι ⁻¹ᵁ U)) (M.val.map (homOfLE (O.ι.image_preimage_le U)).op m))]

/-- The restriction of `φ` to `O` acts on the sections over `U'` as `φ` does on the sections over
the image of `U'` in `X`. -/
theorem restrictFunctor_map_val_app (O : X.Opens) (φ : M ⟶ N) (U' : O.toScheme.Opens)
    (m : M.val.obj (op (O.ι ''ᵁ U'))) :
    ((Scheme.Modules.restrictFunctor O.ι).map φ).val.app (op U') m
      = φ.val.app (op (O.ι ''ᵁ U')) m := rfl

/-- On the restriction to `O` of a morphism `φ` on all of `X`, `valSections` is the action of `φ`
itself on sections. -/
theorem valSections_restrictFunctor_map (O : X.Opens) (φ : M ⟶ N) (U : X.Opens)
    (h : U ≤ O) (m : M.val.obj (op U)) :
    valSections ((Scheme.Modules.restrictFunctor O.ι).map φ) U h m = φ.val.app (op U) m := by
  unfold valSections
  rw [restrictFunctor_map_val_app O φ (O.ι ⁻¹ᵁ U)
      (M.val.map (homOfLE (O.ι.image_preimage_le U)).op m),
    PresheafOfModules.naturality_apply φ.val (homOfLE (O.ι.image_preimage_le U)).op m,
    val_map_homOfLE_self (M := N) (O.ι.image_preimage_le U) (image_preimage_of_le h).ge
      (φ.val.app (op U) m)]

/-- Restricting `θ` to a smaller open `O'` does not change its action on sections over opens
contained in `O'`. -/
theorem valSections_restrictTo {O O' : X.Opens} (hO : O' ≤ O)
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U : X.Opens) (h : U ≤ O') (m : M.val.obj (op U)) :
    valSections (restrictTo hO θ) U h m = valSections θ U (h.trans hO) m :=
  (restrictSections_eq_valSections (restrictTo hO θ) U h m).symm.trans
    ((restrictSections_restrictTo hO θ U h m).trans
      (restrictSections_eq_valSections θ U (h.trans hO) m))


end ValSections

section Comp

variable {X : Scheme.{u}} {M N K : X.Modules}

/-- `restrictHomApp` of a composite is the composite of the two `restrictHomApp`s. -/
theorem restrictHomApp_comp {O : X.Opens}
    (α : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (β : Scheme.Modules.restrict N O.ι ⟶ Scheme.Modules.restrict K O.ι)
    (U' : O.toScheme.Opens) (m : Γ(M, O.ι ''ᵁ U')) :
    restrictHomApp (α ≫ β) U' m = restrictHomApp β U' (restrictHomApp α U' m) := by
  unfold restrictHomApp
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.neg_hom_apply]

/-- `restrictSections` of a composite is the composite of the two `restrictSections`. -/
theorem restrictSections_comp {O : X.Opens}
    (α : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (β : Scheme.Modules.restrict N O.ι ⟶ Scheme.Modules.restrict K O.ι)
    (U : X.Opens) (h : U ≤ O) (m : Γ(M, U)) :
    restrictSections (α ≫ β) U h m = restrictSections β U h (restrictSections α U h m) := by
  unfold restrictSections
  rw [restrictHomApp_comp, modules_presheaf_map_homOfLE_self]

end Comp

section Cross

/-- The inverse comparison of a restricted pullback with the pullback of a restriction, on a
pulled-back section.  This is the `inv` direction of
`Stacks.AlgebraicGeometry.ModuleLimits.restrictPullbackObjIso_hom_pullbackSection`. -/
theorem restrictPullbackObjIso_inv_pullbackSection {Y X : Scheme.{u}} (f : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (F : X.Modules) (U' : X.Opens)
    (V' : V.toScheme.Opens) (h : V.ι ''ᵁ V' ≤ f ⁻¹ᵁ U')
    (h₃ : V' ≤ (Scheme.Hom.resLE f U V e ≫ U.ι) ⁻¹ᵁ U')
    (hf4 : V' ≤ Scheme.Hom.resLE f U V e ⁻¹ᵁ (U.ι ⁻¹ᵁ U'))
    (a : F.val.obj (op U')) :
    (Stacks.Modules.restrictPullbackObjIso f e F).inv.val.app (op V')
        (Scheme.Modules.pullbackSection (Scheme.Hom.resLE f U V e)
          (Scheme.Modules.restrict F U.ι) (U.ι ⁻¹ᵁ U') V' hf4
          (F.val.map (homOfLE (U.ι.image_preimage_le U')).op a))
      = Scheme.Modules.pullbackSection f F U' (V.ι ''ᵁ V') h a := by
  rw [← restrictPullbackObjIso_hom_pullbackSection f e F U' V' h h₃ hf4 a]
  exact congrArg
    (fun k : Scheme.Modules.restrict ((Scheme.Modules.pullback f).obj F) V.ι ⟶
        Scheme.Modules.restrict ((Scheme.Modules.pullback f).obj F) V.ι =>
      k.val.app (op V') (Scheme.Modules.pullbackSection f F U' (V.ι ''ᵁ V') h a))
    (Stacks.Modules.restrictPullbackObjIso f e F).hom_inv_id

/-- The pullback along `γ` of a morphism between the restrictions to an open `Z₀`, as a
morphism between the restrictions of the pullbacks to an open `W₀ ≤ γ⁻¹Z₀`. -/
noncomputable def pullbackRestrictHom {Z P : Scheme.{u}} (γ : P ⟶ Z) {A B : Z.Modules}
    {Z₀ : Z.Opens} {W₀ : P.Opens} (hW : W₀ ≤ γ ⁻¹ᵁ Z₀)
    (Θ : Scheme.Modules.restrict A Z₀.ι ⟶ Scheme.Modules.restrict B Z₀.ι) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback γ).obj A) W₀.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback γ).obj B) W₀.ι :=
  (Stacks.Modules.restrictPullbackObjIso γ hW A).hom ≫
    (Scheme.Modules.pullback (Scheme.Hom.resLE γ Z₀ W₀ hW)).map Θ ≫
      (Stacks.Modules.restrictPullbackObjIso γ hW B).inv

/-- **The pullback of a morphism of restrictions, on a pulled-back section.**  The sectionwise
family of `pullbackRestrictHom γ hW Θ` sends the pullback of a section `y` to the pullback of
the value of `Θ`'s own sectionwise family at `y`. -/
theorem restrictSections_pullbackRestrictHom {Z P : Scheme.{u}} (γ : P ⟶ Z) {A B : Z.Modules}
    {Z₀ : Z.Opens} {W₀ : P.Opens} (hW : W₀ ≤ γ ⁻¹ᵁ Z₀)
    (Θ : Scheme.Modules.restrict A Z₀.ι ⟶ Scheme.Modules.restrict B Z₀.ι)
    (U₁ : Z.Opens) (hU₁ : U₁ ≤ Z₀) (V : P.Opens) (hV : V ≤ W₀) (hVU : V ≤ γ ⁻¹ᵁ U₁)
    (y : A.val.obj (op U₁)) :
    restrictSections (pullbackRestrictHom γ hW Θ) V hV
        (Scheme.Modules.pullbackSection γ A U₁ V hVU y)
      = Scheme.Modules.pullbackSection γ B U₁ V hVU (restrictSections Θ U₁ hU₁ y) := by
  have h1 : W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ V) ≤ γ ⁻¹ᵁ U₁ := (W₀.ι.image_preimage_le V).trans hVU
  have h₃ : (W₀.ι ⁻¹ᵁ V) ≤ (Scheme.Hom.resLE γ Z₀ W₀ hW ≫ Z₀.ι) ⁻¹ᵁ U₁ := by
    rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage]
    exact (W₀.ι.preimage_image_eq _).ge.trans (Scheme.Hom.preimage_mono _ h1)
  have hf4 : (W₀.ι ⁻¹ᵁ V) ≤ Scheme.Hom.resLE γ Z₀ W₀ hW ⁻¹ᵁ (Z₀.ι ⁻¹ᵁ U₁) := by
    rw [← Scheme.Hom.comp_preimage]
    exact h₃
  have hdu : B.val.map (homOfLE (Z₀.ι.image_preimage_le U₁)).op (restrictSections Θ U₁ hU₁ y)
      = Θ.val.app (op (Z₀.ι ⁻¹ᵁ U₁))
        (A.val.map (homOfLE (Z₀.ι.image_preimage_le U₁)).op y) := by
    rw [restrictSections_apply Θ U₁ hU₁ y]
    exact val_map_homOfLE_self _ _ _
  have key : (pullbackRestrictHom γ hW Θ).val.app (op (W₀.ι ⁻¹ᵁ V))
        (Scheme.Modules.pullbackSection γ A U₁ (W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ V)) h1 y)
      = Scheme.Modules.pullbackSection γ B U₁ (W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ V)) h1
          (restrictSections Θ U₁ hU₁ y) := by
    rw [pullbackRestrictHom]
    refine (comp_val_app _ _ _ _).trans ?_
    refine (comp_val_app _ _ _ _).trans ?_
    rw [restrictPullbackObjIso_hom_pullbackSection γ hW A U₁ (W₀.ι ⁻¹ᵁ V) h1 h₃ hf4 y,
      Scheme.Modules.pullbackSection_naturality (Scheme.Hom.resLE γ Z₀ W₀ hW) Θ
        (Z₀.ι ⁻¹ᵁ U₁) (W₀.ι ⁻¹ᵁ V) hf4
        (A.val.map (homOfLE (Z₀.ι.image_preimage_le U₁)).op y),
      ← hdu]
    exact restrictPullbackObjIso_inv_pullbackSection γ hW B U₁ (W₀.ι ⁻¹ᵁ V) h1 h₃ hf4 _
  rw [restrictSections_apply (pullbackRestrictHom γ hW Θ) V hV
      (Scheme.Modules.pullbackSection γ A U₁ V hVU y),
    pullbackSection_shrink γ A U₁ V (W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ V)) hVU
      (W₀.ι.image_preimage_le V) h1 y,
    key]
  exact pullbackSection_shrink γ B U₁ (W₀.ι ''ᵁ (W₀.ι ⁻¹ᵁ V)) V h1
    (image_preimage_of_le hV).ge hVU (restrictSections Θ U₁ hU₁ y)

/-- `restrictSections_pullbackRestrictHom` in the `· .val` spelling. -/
theorem valSections_pullbackRestrictHom {Z P : Scheme.{u}} (γ : P ⟶ Z) {A B : Z.Modules}
    {Z₀ : Z.Opens} {W₀ : P.Opens} (hW : W₀ ≤ γ ⁻¹ᵁ Z₀)
    (Θ : Scheme.Modules.restrict A Z₀.ι ⟶ Scheme.Modules.restrict B Z₀.ι)
    (U₁ : Z.Opens) (hU₁ : U₁ ≤ Z₀) (V : P.Opens) (hV : V ≤ W₀) (hVU : V ≤ γ ⁻¹ᵁ U₁)
    (y : A.val.obj (op U₁)) :
    valSections (pullbackRestrictHom γ hW Θ) V hV
        (Scheme.Modules.pullbackSection γ A U₁ V hVU y)
      = Scheme.Modules.pullbackSection γ B U₁ V hVU (valSections Θ U₁ hU₁ y) :=
  (restrictSections_eq_valSections (pullbackRestrictHom γ hW Θ) V hV
      (Scheme.Modules.pullbackSection γ A U₁ V hVU y)).symm.trans
    ((restrictSections_pullbackRestrictHom γ hW Θ U₁ hU₁ V hV hVU y).trans
      (congrArg (Scheme.Modules.pullbackSection γ B U₁ V hVU)
        (restrictSections_eq_valSections Θ U₁ hU₁ y)))

end Cross

section Predicate

variable {P Z X : Scheme.{u}} (q : P ⟶ Z) (g : Z ⟶ X) (pi : P ⟶ X) (hpi : q ≫ g = pi)
  {F G : X.Modules}
  (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G)

/-- **The canonical equation of [Stacks Project, Tag 01ZR] (2), localized and read on
sections.**  A family `s` of maps on sections over the opens contained in `Z₀`, thought of as a
morphism `g^*F ⟶ g^*G` defined only over `Z₀`, satisfies it when the pullback along `q` of the
value of `s` at a pulled-back section is carried by the canonical identification to the value of
`φ` at the pullback of that section along `pi`. -/
def LocalCanonicalEq (Z₀ : Z.Opens)
    (s : ∀ (W : Z.Opens), W ≤ Z₀ →
      ((Scheme.Modules.pullback g).obj F).val.obj (op W) →
        ((Scheme.Modules.pullback g).obj G).val.obj (op W)) : Prop :=
  ∀ (U : X.Opens) (W : Z.Opens) (hW : W ≤ g ⁻¹ᵁ U) (hWZ : W ≤ Z₀) (V : P.Opens)
    (hV : V ≤ q ⁻¹ᵁ W) (hV' : V ≤ pi ⁻¹ᵁ U) (a : F.val.obj (op U)),
    (canHom q g pi hpi G).val.app (op V)
        (Scheme.Modules.pullbackSection q ((Scheme.Modules.pullback g).obj G) W V hV
          (s W hWZ (Scheme.Modules.pullbackSection g F U W hW a)))
      = φ.val.app (op V) (Scheme.Modules.pullbackSection pi F U V hV' a)

/-- A morphism `Φ : g^*F ⟶ g^*G` whose action on sections satisfies the localized canonical
equation over the whole of `Z` satisfies the canonical equation. -/
theorem canonical_eq_of_localCanonicalEq
    (Φ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (h : LocalCanonicalEq q g pi hpi φ ⊤ (fun W _ => Φ.val.app (op W))) :
    (Scheme.Modules.pullback q).map Φ ≫ canHom q g pi hpi G
      = canHom q g pi hpi F ≫ φ := by
  refine hom_ext_of_doublePullbackSection q g (F := F) fun U a => ?_
  have hV : q ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ q ⁻¹ᵁ (g ⁻¹ᵁ U) := le_rfl
  have hV' : q ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ pi ⁻¹ᵁ U := by rw [← hpi]; exact le_rfl
  refine (comp_val_app _ _ _ _).trans ?_
  refine Eq.trans ?_ (comp_val_app _ _ _ _).symm
  rw [doublePullbackSection,
    Scheme.Modules.pullbackSection_naturality q Φ (g ⁻¹ᵁ U) (q ⁻¹ᵁ (g ⁻¹ᵁ U)) le_rfl
      (Scheme.Modules.pullbackSection g F U (g ⁻¹ᵁ U) le_rfl a),
    canHom_val_app_pullbackSection q g pi hpi F U (g ⁻¹ᵁ U) (q ⁻¹ᵁ (g ⁻¹ᵁ U))
      le_rfl le_rfl hV' a]
  exact h U (g ⁻¹ᵁ U) le_rfl le_top (q ⁻¹ᵁ (g ⁻¹ᵁ U)) le_rfl hV' a

/-- The localized canonical equation for a morphism between the restrictions to `Z₀`. -/
def LocalDescent (Z₀ : Z.Opens)
    (Θ : Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj F) Z₀.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj G) Z₀.ι) : Prop :=
  LocalCanonicalEq q g pi hpi φ Z₀ (valSections Θ)

/-- A local descent datum restricts to a smaller open. -/
theorem localDescent_restrictTo {Z₀ Z₁ : Z.Opens} (hZ : Z₁ ≤ Z₀)
    {Θ : Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj F) Z₀.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj G) Z₀.ι}
    (h : LocalDescent q g pi hpi φ Z₀ Θ) :
    LocalDescent q g pi hpi φ Z₁ (restrictTo hZ Θ) := by
  intro U W hW hWZ V hV hV' a
  simp only [valSections_restrictTo]
  exact h U W hW (hWZ.trans hZ) V hV hV' a

end Predicate

section Transport

variable {P Z Z₂ X : Scheme.{u}} (γ : Z₂ ⟶ Z) (g : Z ⟶ X) (g₂ : Z₂ ⟶ X) (hγ : γ ≫ g = g₂)
  (q : P ⟶ Z) (q₂ : P ⟶ Z₂) (hq : q₂ ≫ γ = q) (pi : P ⟶ X)
  (hpi : q ≫ g = pi) (hpi₂ : q₂ ≫ g₂ = pi) {F G : X.Modules}
  (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G)

/-- The transport of a local descent datum to a later stage: pull back along the transition
morphism `γ` and compose with the canonical identification of `γ^*(g^*F)` with `g₂^*F`. -/
noncomputable def transportRestrictHom {Z₀ : Z.Opens} {W₀ : Z₂.Opens} (hW : W₀ ≤ γ ⁻¹ᵁ Z₀)
    (Θ : Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj F) Z₀.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj G) Z₀.ι) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback g₂).obj F) W₀.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback g₂).obj G) W₀.ι :=
  (Scheme.Modules.restrictFunctor W₀.ι).map (inv (canHom γ g g₂ hγ F)) ≫
    pullbackRestrictHom γ hW Θ ≫
      (Scheme.Modules.restrictFunctor W₀.ι).map (canHom γ g g₂ hγ G)

include hq hpi hpi₂ in
/-- **A local descent datum transports to a later stage.** -/
theorem localDescent_transport {Z₀ : Z.Opens} {W₀ : Z₂.Opens} (hW : W₀ ≤ γ ⁻¹ᵁ Z₀)
    (Θ : Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj F) Z₀.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj G) Z₀.ι)
    (h : LocalDescent q g pi hpi φ Z₀ Θ) :
    LocalDescent q₂ g₂ pi hpi₂ φ W₀ (transportRestrictHom γ g g₂ hγ hW Θ) := by
  intro U W hW2 hWZ V hV hV' a
  obtain ⟨U₁, hU₁g, hU₁Z, hWU₁⟩ : ∃ T : Z.Opens, T ≤ g ⁻¹ᵁ U ∧ T ≤ Z₀ ∧ W ≤ γ ⁻¹ᵁ T := by
    refine ⟨(g ⁻¹ᵁ U) ⊓ Z₀, inf_le_left, inf_le_right, ?_⟩
    show W ≤ (γ ⁻¹ᵁ (g ⁻¹ᵁ U)) ⊓ (γ ⁻¹ᵁ Z₀)
    exact le_inf (by rw [← Scheme.Hom.comp_preimage, hγ]; exact hW2) (hWZ.trans hW)
  have hVq : V ≤ q ⁻¹ᵁ U₁ := by
    rw [← hq, Scheme.Hom.comp_preimage]
    exact hV.trans (Scheme.Hom.preimage_mono _ hWU₁)
  have hstep : valSections (transportRestrictHom γ g g₂ hγ hW Θ) W hWZ
        (Scheme.Modules.pullbackSection g₂ F U W hW2 a)
      = (canHom γ g g₂ hγ G).val.app (op W)
          (Scheme.Modules.pullbackSection γ ((Scheme.Modules.pullback g).obj G) U₁ W hWU₁
            (valSections Θ U₁ hU₁Z (Scheme.Modules.pullbackSection g F U U₁ hU₁g a))) := by
    rw [transportRestrictHom,
      valSections_comp ((Scheme.Modules.restrictFunctor W₀.ι).map (inv (canHom γ g g₂ hγ F)))
        (pullbackRestrictHom γ hW Θ ≫
          (Scheme.Modules.restrictFunctor W₀.ι).map (canHom γ g g₂ hγ G)) W hWZ
        (Scheme.Modules.pullbackSection g₂ F U W hW2 a),
      valSections_restrictFunctor_map W₀ (inv (canHom γ g g₂ hγ F)) W hWZ
        (Scheme.Modules.pullbackSection g₂ F U W hW2 a),
      canHom_inv_val_app_pullbackSection γ g g₂ hγ F U U₁ W hU₁g hWU₁ hW2 a,
      valSections_comp (pullbackRestrictHom γ hW Θ)
        ((Scheme.Modules.restrictFunctor W₀.ι).map (canHom γ g g₂ hγ G)) W hWZ
        (Scheme.Modules.pullbackSection γ ((Scheme.Modules.pullback g).obj F) U₁ W hWU₁
          (Scheme.Modules.pullbackSection g F U U₁ hU₁g a)),
      valSections_pullbackRestrictHom γ hW Θ U₁ hU₁Z W hWZ hWU₁
        (Scheme.Modules.pullbackSection g F U U₁ hU₁g a),
      valSections_restrictFunctor_map W₀ (canHom γ g g₂ hγ G) W hWZ
        (Scheme.Modules.pullbackSection γ ((Scheme.Modules.pullback g).obj G) U₁ W hWU₁
          (valSections Θ U₁ hU₁Z (Scheme.Modules.pullbackSection g F U U₁ hU₁g a)))]
  rw [hstep, ← Scheme.Modules.pullbackSection_naturality q₂ (canHom γ g g₂ hγ G) W V hV
      (Scheme.Modules.pullbackSection γ ((Scheme.Modules.pullback g).obj G) U₁ W hWU₁
        (valSections Θ U₁ hU₁Z (Scheme.Modules.pullbackSection g F U U₁ hU₁g a))),
    ← comp_val_app, canHom_cocycle q₂ γ g q g₂ pi hq hγ hpi hpi₂ G, comp_val_app,
    canHom_val_app_pullbackSection q₂ γ q hq ((Scheme.Modules.pullback g).obj G) U₁ W V
      hWU₁ hV hVq
      (valSections Θ U₁ hU₁Z (Scheme.Modules.pullbackSection g F U U₁ hU₁g a))]
  exact h U U₁ hU₁g hU₁Z V hVq hV' a

end Transport

end Stacks.AlgebraicGeometry.ModuleLimits

end
