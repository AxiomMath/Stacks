module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Descent

/-!
# Degree-zero flat base change for the sections of a quasi-coherent module

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `S` and `S'` affine, `g` flat and `f` quasi-compact and
quasi-separated, and let `F` be a quasi-coherent `O_X`-module. This file proves that

  `Gamma(S', O_{S'}) (x)_{Gamma(S, O_S)} Gamma(X, F) = Gamma(X', (g')^* F)`,

which is [Stacks, Tag 02KH] part (2) in degree `i = 0`, for a module rather than for the
structure sheaf. Mathlib proves the structure-sheaf case over all of `X` — it is
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`, and that result is
used here for the base ring — but its `pushoutSection` family covers only `O_X`.

## Main definitions

* `Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections`: the unit of `g'^* ⊣ g'_*`
  read on sections, which is the canonical base-change comparison.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.baseAlgebra` and `baseModule`: the scalar
  structures over `Gamma(S, O_S)` that the statements are about. They are restrictions of
  scalars along the structure morphism, so they are not instances.

## Main results

* `Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange`:
  **the theorem.** The canonical map
  `Gamma(S', O_{S'}) (x)_{Gamma(S, O_S)} Gamma(X, F) ⟶ Gamma(X', (g')^* F)` is an isomorphism.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.isBaseChange_appTop_pullbackSections`: the same
  statement read over the global functions, `Gamma(X', O_{X'}) (x)_{Gamma(X, O_X)} Gamma(X, F)`.
  This is the form Tag 0CDX consumes, because the ring map it descends invertibility along is
  `Gamma(X, O_X) ⟶ Gamma(X', O_{X'})`.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.isBaseChange_appTop_pullbackSections_of_flat`:
  that form for a base change along a flat ring map `phi : A →+* B`.
* `Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections_naturality_module`:
  **naturality in the module.** Together with the normalisation on pure tensors this identifies
  the isomorphism as the canonical comparison, natural in `F`, and not an unconstrained one.

## Implementation notes

The proof is the Cech argument of the Stacks proof, run as the local-to-global induction of
`StacksFrontier/AlgebraicGeometry/PullbackSections/Descent.lean`:

* over a pair of affine opens the comparison is
  `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` of
  `StacksFrontier/AlgebraicGeometry/PullbackSections/Affine.lean`, normalised on `1 (x) a` by
  `affinePullbackSectionsBaseChangeIso_one_tmul`, transported to the base ring pair by
  `Algebra.IsPushout.cancelBaseChange` along the affine case of Mathlib's `pushoutSection`;
* over a quasi-compact open it is injective, by a finite affine cover and flatness;
* over a quasi-separated quasi-compact open it is bijective, by induction on a finite affine
  cover with the Mayer-Vietoris step.

Both sheaves are read on the opens of `X`: the target is the sections of `(g')^* F` over the
preimage, which is a sheaf on `X` because `g'^{-1}` preserves suprema and infima. The scalar
structures are restrictions of scalars and are therefore passed explicitly rather than
synthesised; `Stacks.FlatSectionsDescent.isScalarTower_of_smul_eq` and
`map_smul_of_smul_eq` do the comparisons once, at abstract types, and are applied, because the
corresponding defeq is ruinous at a concrete sheaf-section type.

`Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSection_eq_pullbackUnitSections` duplicates
`Stacks.Conormal.pullbackSection_self` of
`StacksFrontier/AlgebraicGeometry/ConormalAlgebra/GradedPullback.lean`, which is stated in the
`val.app` spelling in a namespace that is local to that file; the two are the same fact.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.FlatSectionsDescent
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.SectionsBaseChange

variable {S T X Y : Scheme.{u}}

/-- Every open is contained in the preimage of the whole base. -/
theorem le_preimage_top (f : X ⟶ S) (U : X.Opens) : U ≤ f ⁻¹ᵁ (⊤ : S.Opens) := by simp

/-! ### Scalar structures over the base -/

/-- The `Γ(S, ⊤)`-algebra structure on `Γ(T, ⊤)` given by a morphism `q : T ⟶ S`. -/
@[instance_reducible]
def baseAlgebra (q : T ⟶ S) : Algebra Γ(S, ⊤) Γ(T, ⊤) :=
  (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom.toAlgebra

/-- The `Γ(W, ⊤)`-module structure on the sections of an `𝒪_Z`-module over an open of `Z`,
given a morphism `h : Z ⟶ W`. -/
@[instance_reducible]
def baseModule {Z W : Scheme.{u}} (h : Z ⟶ W) (M : Z.Modules) (U : Z.Opens) :
    Module Γ(W, ⊤) Γ(M, U) :=
  Module.compHom _ (h.appLE ⊤ U (le_preimage_top h U)).hom

/-- **The two ways round a cartesian square agree on sections.** -/
theorem sectionsSquare_comm {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}
    (H : IsPullback p k iX q) (V : Y.Opens) (a : Γ(S, ⊤)) :
    ((p ≫ iX).appLE ⊤ V (le_preimage_top (p ≫ iX) V)).hom a =
      (k.appLE ⊤ V (le_preimage_top k V)).hom
        ((q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom a) := by
  have e1 : q.appLE ⊤ ⊤ (le_preimage_top q ⊤) ≫ k.appLE ⊤ V (le_preimage_top k V) =
      (k ≫ q).appLE ⊤ V _ := Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  exact congrArg (fun m : Γ(S, ⊤) ⟶ Γ(Y, V) => m.hom a)
    ((congrArg (fun m : Y ⟶ S => m.appLE ⊤ V (le_preimage_top m V)) H.w).trans e1.symm)

/-- A section of the base, restricted to `p ⁻¹ᵁ U`, factors through `Γ(X, U)`. -/
theorem appLE_comp_base (iX : X ⟶ S) (p : Y ⟶ X) (U : X.Opens) (a : Γ(S, ⊤)) :
    ((p ≫ iX).appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top (p ≫ iX) _)).hom a =
      (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom ((iX.appLE ⊤ U (le_preimage_top iX U)).hom a) := by
  have e1 : iX.appLE ⊤ U (le_preimage_top iX U) ≫ p.appLE U (p ⁻¹ᵁ U) le_rfl =
      (p ≫ iX).appLE ⊤ (p ⁻¹ᵁ U) _ := Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  exact (congrArg (fun m : Γ(S, ⊤) ⟶ Γ(Y, p ⁻¹ᵁ U) => m.hom a) e1).symm

/-- The base scalar structures on the sections of a module on the pullback form a tower. -/
theorem baseTower {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}
    (H : IsPullback p k iX q) (G : Y.Modules) (V : Y.Opens) :
    letI := baseAlgebra q
    letI := baseModule (p ≫ iX) G V
    letI := baseModule k G V
    IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(G, V) :=
  let := baseAlgebra q
  let := baseModule (p ≫ iX) G V
  let := baseModule k G V
  Stacks.FlatSectionsDescent.isScalarTower_of_smul_eq _ (fun _ _ => rfl) _ (fun _ _ => rfl)
    (sectionsSquare_comm H V)

/-! ### Sections of a pullback -/

/-- The unit of `p^* ⊣ p_*` read on sections over `U`, as an additive map into the sections of
`p^* F` over `p ⁻¹ᵁ U`. -/
noncomputable def pullbackUnitSections (p : Y ⟶ X) (F : X.Modules) (U : X.Opens) :
    Γ(F, U) →+ Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).app U).hom

/-- Restricting the unit on sections gives the pullback of a section. -/
theorem map_pullbackUnitSections (p : Y ⟶ X) (F : X.Modules) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ p ⁻¹ᵁ U) (a : Γ(F, U)) :
    ((Scheme.Modules.pullback p).obj F).presheaf.map (homOfLE h).op (pullbackUnitSections p F U a) =
      (Scheme.Modules.pullbackSection p F U V h a :
        Γ((Scheme.Modules.pullback p).obj F, V)) := rfl

/-- **The pullback of a section**, as an additive map, with the target open named explicitly.
Its underlying function is `AlgebraicGeometry.Scheme.Modules.pullbackSection`. -/
def pullbackSectionsHom (p : Y ⟶ X) (F : X.Modules) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ p ⁻¹ᵁ U) : Γ(F, U) →+ Γ((Scheme.Modules.pullback p).obj F, V) :=
  (((Scheme.Modules.pullback p).obj F).presheaf.map (homOfLE h).op).hom.comp
    (pullbackUnitSections p F U)

/-- `pullbackSectionsHom p F U V h` sends a section `a` to its pullback
`Scheme.Modules.pullbackSection p F U V h a`. -/
theorem pullbackSectionsHom_apply (p : Y ⟶ X) (F : X.Modules) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ p ⁻¹ᵁ U) (a : Γ(F, U)) :
    pullbackSectionsHom p F U V h a =
      (Scheme.Modules.pullbackSection p F U V h a :
        Γ((Scheme.Modules.pullback p).obj F, V)) := rfl

/-- The unit on sections is semilinear along `p.app U`. -/
theorem pullbackUnitSections_smul (p : Y ⟶ X) (F : X.Modules) (U : X.Opens) (r : Γ(X, U))
    (a : Γ(F, U)) :
    pullbackUnitSections p F U (r • a) = (p.app U).hom r • pullbackUnitSections p F U a :=
  Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F) r a

/-- **The comparison is natural in the module.** For a morphism `t : F ⟶ F'` of
`𝒪_X`-modules, pulling a section back and then applying `p^* t` is applying `t` and then pulling
back. -/
theorem pullbackUnitSections_naturality_module (p : Y ⟶ X) {F F' : X.Modules} (t : F ⟶ F')
    (U : X.Opens) (a : Γ(F, U)) :
    ((Scheme.Modules.pullback p).map t).app (p ⁻¹ᵁ U) (pullbackUnitSections p F U a) =
      pullbackUnitSections p F' U (t.app U a) :=
  Scheme.Modules.unit_app_val_app_naturality p t U a

/-- The unit on sections is natural in the open. -/
theorem pullbackUnitSections_naturality (p : Y ⟶ X) (F : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (a : Γ(F, U)) :
    pullbackUnitSections p F V (F.presheaf.map (homOfLE h).op a) =
      ((Scheme.Modules.pullback p).obj F).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono p h)).op (pullbackUnitSections p F U a) := by
  have hnat : F.presheaf.map (homOfLE h).op ≫
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).app V =
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).app U ≫
        ((Scheme.Modules.pushforward p).obj
          ((Scheme.Modules.pullback p).obj F)).presheaf.map (homOfLE h).op :=
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).mapPresheaf.naturality
      (homOfLE h).op
  exact congrArg (fun (t : Γ(F, U) ⟶ Γ((Scheme.Modules.pushforward p).obj
    ((Scheme.Modules.pullback p).obj F), V)) => ConcreteCategory.hom t a) hnat

/-! ### Gluing two sections of a sheaf of abelian groups -/

/-- Two sections of a sheaf agreeing on the intersection glue over the union. -/
theorem sheaf_glue_pair {Z : TopCat.{u}} (sh : TopCat.Sheaf Ab.{u} Z) (U₁ U₂ : Opens Z)
    (x₁ : sh.1.obj (op U₁)) (x₂ : sh.1.obj (op U₂))
    (hx : sh.1.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op x₁ =
      sh.1.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op x₂) :
    ∃ y : sh.1.obj (op (U₁ ⊔ U₂)),
      sh.1.map (homOfLE (le_sup_left : U₁ ≤ U₁ ⊔ U₂)).op y = x₁ ∧
      sh.1.map (homOfLE (le_sup_right : U₂ ≤ U₁ ⊔ U₂)).op y = x₂ := by
  classical
  have hcover : U₁ ⊔ U₂ ≤ ⨆ b : Bool, cond b U₂ U₁ := by
    rw [iSup_bool_eq]
    exact le_of_eq (sup_comm U₁ U₂)
  have hle : ∀ b : Bool, cond b U₂ U₁ ≤ U₁ ⊔ U₂ := fun b => by cases b <;> simp
  have key : ∀ (V W : Opens Z) (_ : V ⊓ W ≤ U₁ ⊓ U₂) (h₁ : V ⊓ W ≤ U₁) (h₂ : V ⊓ W ≤ U₂),
      sh.1.map (homOfLE h₁).op x₁ = sh.1.map (homOfLE h₂).op x₂ := by
    intro V W hV h₁ h₂
    have e := congrArg (sh.1.map (homOfLE hV).op) hx
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← sh.1.map_comp,
      ← sh.1.map_comp] at e
  have hcpt : TopCat.Presheaf.IsCompatible sh.1 (fun b : Bool => cond b U₂ U₁)
      (fun b => match b with | true => x₂ | false => x₁) := by
    intro b₁ b₂
    cases b₁ <;> cases b₂
    · rfl
    · exact key U₁ U₂ le_rfl inf_le_left inf_le_right
    · exact (key U₂ U₁ (by rw [inf_comm]) inf_le_right inf_le_left).symm
    · rfl
  obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing' sh (fun b : Bool => cond b U₂ U₁)
    (U₁ ⊔ U₂) (fun b => homOfLE (hle b)) hcover
    (fun b => match b with | true => x₂ | false => x₁) hcpt
  exact ⟨y, hy false, hy true⟩

/-- **The sections square over an open of `X` is a pushout of rings**, whenever Mathlib's
`AlgebraicGeometry.pushoutSection` is an isomorphism there. -/
theorem algebraIsPushout_sections {q : T ⟶ S} {iX : X ⟶ S}
    {p : Y ⟶ X} {k : Y ⟶ T} (H : IsPullback p k iX q) (U : X.Opens) (UY : Y.Opens)
    (hUST : (⊤ : T.Opens) ≤ q ⁻¹ᵁ (⊤ : S.Opens)) (hUSX : U ≤ iX ⁻¹ᵁ (⊤ : S.Opens))
    (hUY : UY = p ⁻¹ᵁ U ⊓ k ⁻¹ᵁ (⊤ : T.Opens))
    (hiso : IsIso (pushoutSection H hUST hUSX hUY))
    (hp' : UY ≤ p ⁻¹ᵁ U) (hk' : UY ≤ k ⁻¹ᵁ (⊤ : T.Opens))
    [Algebra Γ(S, ⊤) Γ(T, ⊤)]
    (h1 : ∀ r, algebraMap Γ(S, ⊤) Γ(T, ⊤) r = (q.appLE ⊤ ⊤ hUST).hom r)
    [Algebra Γ(S, ⊤) Γ(X, U)]
    (h2 : ∀ r, algebraMap Γ(S, ⊤) Γ(X, U) r = (iX.appLE ⊤ U hUSX).hom r)
    [Algebra Γ(T, ⊤) Γ(Y, UY)]
    (h3 : ∀ r, algebraMap Γ(T, ⊤) Γ(Y, UY) r = (k.appLE ⊤ UY hk').hom r)
    [Algebra Γ(X, U) Γ(Y, UY)]
    (h4 : ∀ r, algebraMap Γ(X, U) Γ(Y, UY) r = (p.appLE U UY hp').hom r)
    [Algebra Γ(S, ⊤) Γ(Y, UY)]
    [IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, UY)]
    [IsScalarTower Γ(S, ⊤) Γ(X, U) Γ(Y, UY)] :
    Algebra.IsPushout Γ(S, ⊤) Γ(T, ⊤) Γ(X, U) Γ(Y, UY) := by
  have key : ∀ {A B : CommRingCat} [Algebra A B] (f : A ⟶ B),
      (∀ r, algebraMap A B r = f.hom r) → CommRingCat.ofHom (algebraMap A B) = f :=
    fun _ h => CommRingCat.hom_ext (RingHom.ext h)
  rw [← CommRingCat.isPushout_iff_isPushout, key _ h1, key _ h2, key _ h3, key _ h4]
  exact ((isIso_pushoutSection_iff H hUST hUSX hUY).mp hiso).flip

/-- Over the whole preimage, the pullback of a section is the unit read on sections. -/
theorem pullbackSection_eq_pullbackUnitSections (p : Y ⟶ X) (F : X.Modules) (U : X.Opens)
    (a : Γ(F, U)) :
    (Scheme.Modules.pullbackSection p F U (p ⁻¹ᵁ U) le_rfl a :
        Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)) = pullbackUnitSections p F U a := by
  rw [← map_pullbackUnitSections p F U (p ⁻¹ᵁ U) le_rfl,
    show (homOfLE (le_refl (p ⁻¹ᵁ U))).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

/-- Over the whole space the pullback of a section is the unit read on sections. -/
theorem pullbackSectionsHom_top (p : Y ⟶ X) (F : X.Modules) (a : Γ(F, ⊤)) :
    pullbackSectionsHom p F ⊤ ⊤ (le_preimage_top p ⊤) a = pullbackUnitSections p F ⊤ a :=
  pullbackSection_eq_pullbackUnitSections p F ⊤ a

/-- A quasi-compact open of a scheme is covered by finitely many affine opens inside it. -/
private theorem exists_finite_affine_cover {U : X.Opens} (hU : IsCompact (X := X) U) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.Opens),
      (∀ i, IsAffineOpen (V i)) ∧ (∀ i, V i ≤ U) ∧ U ≤ ⨆ i, V i := by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  refine ⟨I, hI.to_subtype, fun i => i.1, fun i => i.1.2, fun i => ?_,
    le_of_eq (by rw [e, iSup_subtype'])⟩
  rw [e]
  exact le_iSup_of_le i.1 (le_iSup_of_le i.2 le_rfl)

/-- **Stacks Project, Tag 02KH, part (2), in degree zero.** Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `S` and `S'` affine, `g` flat and `f` quasi-compact and
quasi-separated, and let `F` be a quasi-coherent `𝒪_X`-module. Then the canonical map

  `Γ(S', 𝒪_{S'}) ⊗_{Γ(S, 𝒪_S)} Γ(X, F) ⟶ Γ(X', (g')^* F)`

sending `b ⊗ a` to `b • (g')^* a` is an isomorphism.

The comparison is pinned down by its values on pure tensors, through
`Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections`, which is natural in `F` by
`pullbackUnitSections_naturality_module`; so the isomorphism is the canonical base-change map
and not an unconstrained one.

Part (2) of [Stacks, Tag 02KH] in every degree is
`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.cohomologyBaseChangeIso`. -/
theorem exists_linearEquiv_sections_baseChange
    {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T} (H : IsPullback p k iX q)
    [IsAffine S] [IsAffine T] [Flat q] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] :
    letI := baseAlgebra q
    letI := baseModule iX F ⊤
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) ⊤
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) ⊤
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) ⊤
    ∃ e : Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(F, ⊤) ≃ₗ[Γ(T, ⊤)]
        Γ((Scheme.Modules.pullback p).obj F, ⊤),
      ∀ (b : Γ(T, ⊤)) (a : Γ(F, ⊤)),
        e (b ⊗ₜ[Γ(S, ⊤)] a) = b • pullbackSectionsHom p F ⊤ ⊤ (le_preimage_top p ⊤) a := by
  classical
  have hpaff : IsAffineHom p := MorphismProperty.of_isPullback H.flip inferInstance
  -- the base ring map
  let algAB : Algebra Γ(S, ⊤) Γ(T, ⊤) := baseAlgebra q
  have flatAB : Module.Flat Γ(S, ⊤) Γ(T, ⊤) :=
    Flat.flat_appLE q (isAffineOpen_top S) (isAffineOpen_top T) (le_preimage_top q ⊤)
  -- scalar structures over the base
  let modAF : ∀ U : X.Opens, Module Γ(S, ⊤) Γ(F, U) := fun U => baseModule iX F U
  have hmodAF : ∀ (U : X.Opens) (a : Γ(S, ⊤)) (x : Γ(F, U)),
      a • x = (iX.appLE ⊤ U (le_preimage_top iX U)).hom a • x := fun _ _ _ => rfl
  let modAG : ∀ U : X.Opens,
      Module Γ(S, ⊤) Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) := fun U =>
    baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  have hmodAG : ∀ (U : X.Opens) (a : Γ(S, ⊤))
      (y : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)),
      a • y = ((p ≫ iX).appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top (p ≫ iX) _)).hom a • y :=
    fun _ _ _ => rfl
  let modBG : ∀ U : X.Opens,
      Module Γ(T, ⊤) Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) := fun U =>
    baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  have hmodBG : ∀ (U : X.Opens) (b : Γ(T, ⊤))
      (y : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)),
      b • y = (k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom b • y := fun _ _ _ => rfl
  have hcomm : ∀ (U : X.Opens) (a : Γ(S, ⊤)),
      ((p ≫ iX).appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top (p ≫ iX) _)).hom a =
      (k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom
        ((q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom a) :=
    fun U => sectionsSquare_comm H (p ⁻¹ᵁ U)
  have towerG : ∀ U : X.Opens,
      IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) := fun U =>
    baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  -- the comparison map, open by open
  have hpapp : ∀ U : X.Opens, ∀ a : Γ(S, ⊤),
      ((p ≫ iX).appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top (p ≫ iX) _)).hom a =
        (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom ((iX.appLE ⊤ U (le_preimage_top iX U)).hom a) :=
    fun U => appLE_comp_base iX p U
  have hunitsmul : ∀ (U : X.Opens) (r : Γ(X, U)) (a : Γ(F, U)),
      pullbackUnitSections p F U (r • a) =
        (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom r • pullbackUnitSections p F U a := by
    intro U r a
    rw [Scheme.Hom.appLE_preimage_self]
    exact pullbackUnitSections_smul p F U r a
  let cmp : ∀ U : X.Opens,
      Γ(F, U) →ₗ[Γ(S, ⊤)] Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) := fun U =>
    { toFun := pullbackUnitSections p F U
      map_add' := (pullbackUnitSections p F U).map_add
      map_smul' := fun a x =>
        map_smul_of_smul_eq _ (hmodAF U) _ (hmodAG U)
          (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom (hpapp U)
          (pullbackUnitSections p F U) (hunitsmul U) a x }
  -- restriction maps
  have hresX : ∀ {U V : X.Opens} (h : V ≤ U) (a : Γ(S, ⊤)),
      (iX.appLE ⊤ V (le_preimage_top iX V)).hom a =
        (X.presheaf.map (homOfLE h).op).hom ((iX.appLE ⊤ U (le_preimage_top iX U)).hom a) := by
    intro U V h a
    exact (congrArg (fun m : Γ(S, ⊤) ⟶ Γ(X, V) => m.hom a)
      (Scheme.Hom.appLE_map iX (le_preimage_top iX U) (homOfLE h).op)).symm
  have hresY : ∀ {U V : X.Opens} (h : V ≤ U) (b : Γ(T, ⊤)),
      (k.appLE ⊤ (p ⁻¹ᵁ V) (le_preimage_top k _)).hom b =
        (Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono p h)).op).hom
          ((k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom b) := by
    intro U V h b
    exact (congrArg (fun m : Γ(T, ⊤) ⟶ Γ(Y, p ⁻¹ᵁ V) => m.hom b)
      (Scheme.Hom.appLE_map k (le_preimage_top k _)
        (homOfLE (Scheme.Hom.preimage_mono p h)).op)).symm
  let resM : ∀ {U V : X.Opens}, V ≤ U → (Γ(F, U) →ₗ[Γ(S, ⊤)] Γ(F, V)) := fun {U V} h =>
    { toFun := (F.presheaf.map (homOfLE h).op).hom
      map_add' := (F.presheaf.map (homOfLE h).op).hom.map_add
      map_smul' := fun a x =>
        map_smul_of_smul_eq _ (hmodAF U) _ (hmodAF V)
          (X.presheaf.map (homOfLE h).op).hom (hresX h) _
          (fun r y => Scheme.Modules.map_smul F (homOfLE h) r y) a x }
  let resN : ∀ {U V : X.Opens}, V ≤ U →
      (Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) →ₗ[Γ(T, ⊤)]
        Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ V)) := fun {U V} h =>
    { toFun := (((Scheme.Modules.pullback p).obj F).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono p h)).op).hom
      map_add' := (((Scheme.Modules.pullback p).obj F).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono p h)).op).hom.map_add
      map_smul' := fun b y =>
        map_smul_of_smul_eq _ (hmodBG U) _ (hmodBG V)
          (Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono p h)).op).hom (hresY h) _
          (fun r z => Scheme.Modules.map_smul ((Scheme.Modules.pullback p).obj F)
            (homOfLE (Scheme.Hom.preimage_mono p h)) r z) b y }
  -- the comparison datum
  let c : Comparison Γ(S, ⊤) Γ(T, ⊤) X.Opens (fun U => Γ(F, U))
      (fun U => Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)) :=
    { resM := fun {_ _} h => resM h
      resN := fun {_ _} h => resN h
      cmp := cmp
      resM_resM := by
        intro U V W h₁ h₂ x
        show (F.presheaf.map (homOfLE h₂).op).hom ((F.presheaf.map (homOfLE h₁).op).hom x) =
          (F.presheaf.map (homOfLE (h₂.trans h₁)).op).hom x
        rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
        rfl
      resN_resN := by
        intro U V W h₁ h₂ y
        show (((Scheme.Modules.pullback p).obj F).presheaf.map
            (homOfLE (Scheme.Hom.preimage_mono p h₂)).op).hom
          ((((Scheme.Modules.pullback p).obj F).presheaf.map
            (homOfLE (Scheme.Hom.preimage_mono p h₁)).op).hom y) = _
        rw [← ConcreteCategory.comp_apply, ← ((Scheme.Modules.pullback p).obj F).presheaf.map_comp]
        rfl
      cmp_res := by
        intro U V h x
        exact pullbackUnitSections_naturality p F h x
      sepM := by
        intro U cov hcov hU x hx
        refine TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab.{u} _)
          (fun V : {V : X.Opens // V ∈ cov} => (V : X.Opens)) U
          (fun V => homOfLE (hcov V.1 V.2)) (by rw [← sSup_eq_iSup']; exact hU) x 0 (fun V => ?_)
        rw [map_zero]
        exact hx V.1 V.2
      sepN := by
        intro U cov hcov hU y hy
        refine TopCat.Sheaf.eq_of_locally_eq'
          (⟨((Scheme.Modules.pullback p).obj F).presheaf,
            ((Scheme.Modules.pullback p).obj F).isSheaf⟩ : TopCat.Sheaf Ab.{u} _)
          (fun V : {V : X.Opens // V ∈ cov} => p ⁻¹ᵁ (V : X.Opens)) (p ⁻¹ᵁ U)
          (fun V => homOfLE (Scheme.Hom.preimage_mono p (hcov V.1 V.2))) ?_ y 0 (fun V => ?_)
        · rw [← Scheme.Hom.preimage_iSup]
          exact Scheme.Hom.preimage_mono p (by rw [← sSup_eq_iSup']; exact hU)
        · rw [map_zero]
          exact hy V.1 V.2
      glueM := by
        intro U₁ U₂ x₁ x₂ hx
        exact sheaf_glue_pair (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab.{u} _) U₁ U₂ x₁ x₂ hx }
  -- the affine case
  have hUST : (⊤ : T.Opens) ≤ q ⁻¹ᵁ (⊤ : S.Opens) := le_preimage_top q ⊤
  have haff : ∀ U : X.Opens, IsAffineOpen U → Function.Bijective (c.baseChangeMap U) := by
    intro U hU
    have hV : IsAffineOpen (p ⁻¹ᵁ U) := hU.preimage p
    let algAX : Algebra Γ(S, ⊤) Γ(X, U) :=
      (iX.appLE ⊤ U (le_preimage_top iX U)).hom.toAlgebra
    let algAY : Algebra Γ(S, ⊤) Γ(Y, p ⁻¹ᵁ U) :=
      ((p ≫ iX).appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top (p ≫ iX) _)).hom.toAlgebra
    let algBY : Algebra Γ(T, ⊤) Γ(Y, p ⁻¹ᵁ U) :=
      (k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom.toAlgebra
    let algXY : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
      (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    have towerAXY : IsScalarTower Γ(S, ⊤) Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
      isScalarTower_of_smul_eq (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom (fun _ _ => rfl) _
        (fun _ _ => rfl) (hpapp U)
    have towerATY : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, p ⁻¹ᵁ U) :=
      isScalarTower_of_smul_eq (k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom (fun _ _ => rfl) _
        (fun _ _ => rfl) (hcomm U)
    have towerAXF : IsScalarTower Γ(S, ⊤) Γ(X, U) Γ(F, U) :=
      isScalarTower_of_smul_eq (RingHom.id _) (fun _ _ => rfl) _ (hmodAF U) (fun _ => rfl)
    have hpo : Algebra.IsPushout Γ(S, ⊤) Γ(T, ⊤) Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
      algebraIsPushout_sections H U (p ⁻¹ᵁ U) hUST (le_preimage_top iX U) (by simp)
        (isIso_pushoutSection_of_isAffineOpen H hUST (le_preimage_top iX U) (by simp)
          (isAffineOpen_top S) (isAffineOpen_top T) hU)
        le_rfl (le_preimage_top k _) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    let modXG : Module Γ(X, U) Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
      Module.compHom _ (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom
    have towerXYG : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U)
        Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
      isScalarTower_of_smul_eq (RingHom.id _) (fun _ _ => rfl)
        (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom (fun _ _ => rfl) (fun _ => rfl)
    let rhoU : Γ(F, U) →ₗ[Γ(X, U)] Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
      { toFun := pullbackUnitSections p F U
        map_add' := (pullbackUnitSections p F U).map_add
        map_smul' := fun r x => hunitsmul U r x }
    have hbc : IsBaseChange Γ(Y, p ⁻¹ᵁ U) rhoU :=
      AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso
        (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom rfl
        (affinePullbackSectionsBaseChangeIso p F hU hV le_rfl) rhoU (fun m => by
          rw [affinePullbackSectionsBaseChangeIso_one_tmul]
          exact pullbackSection_eq_pullbackUnitSections p F U m)
    let can := Algebra.IsPushout.cancelBaseChange Γ(S, ⊤) Γ(T, ⊤) Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Γ(F, U)
    let g : Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(F, U) ≃+
        Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
      (can.symm.toAddEquiv).trans hbc.equiv.toAddEquiv
    show Function.Bijective ((c.cmp U).liftBaseChange Γ(T, ⊤))
    refine bijective_liftBaseChange_of_tmul (c.cmp U) g.toAddMonoidHom g.bijective ?_
    intro b m
    show hbc.equiv (can.symm (b ⊗ₜ[Γ(S, ⊤)] m)) = _
    rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, hbc.equiv_tmul]
    rfl
  -- injectivity on quasi-compact opens
  have hcpt : ∀ U : X.Opens, IsCompact (X := X) U → Function.Injective (c.baseChangeMap U) := by
    intro U hcU
    obtain ⟨ι, _, V, hV, hVU, hUV⟩ := exists_finite_affine_cover hcU
    exact c.injective_baseChangeMap_of_iSup U V hVU hUV fun i => (haff _ (hV i)).injective
  -- the global case
  have htop : Function.Bijective (c.baseChangeMap ⊤) := by
    obtain ⟨ι, _, V, hV, hVU, hUV⟩ := exists_finite_affine_cover
      (show IsCompact (X := X) (⊤ : X.Opens) by simpa using isCompact_univ)
    refine c.bijective_baseChangeMap_of_iSup ⊤ V hVU hUV (fun i => haff _ (hV i)) (fun i j => ?_)
    refine hcpt _ ?_
    simpa using (isQuasiSeparated_univ : IsQuasiSeparated (Set.univ : Set X)) (V i : Set X)
      (V j : Set X) (Set.subset_univ _) (V i).isOpen (hV i).isCompact (Set.subset_univ _)
      (V j).isOpen (hV j).isCompact
  refine ⟨LinearEquiv.ofBijective (c.baseChangeMap ⊤) htop, fun b a => ?_⟩
  show (c.cmp ⊤).liftBaseChange Γ(T, ⊤) (b ⊗ₜ[Γ(S, ⊤)] a) = _
  rw [LinearMap.liftBaseChange_tmul, pullbackSectionsHom_top]
  rfl

/-- **Degree-zero flat base change over the global functions.** In the situation of
`Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange`, pulling a
section back exhibits `Γ(X', (g')^* F)` as `Γ(X', 𝒪_{X'}) ⊗_{Γ(X, 𝒪_X)} Γ(X, F)`.

This is the form in which Tag 0CDX uses degree-zero flat base change: the ring map it descends
invertibility along is `Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})`, not `Γ(S, 𝒪_S) ⟶ Γ(S', 𝒪_{S'})`.

The `Γ(X, ⊤)`-algebra structure on `Γ(X', ⊤)` and the `Γ(X, ⊤)`-module structure on the sections
of the pullback are restrictions of scalars along `g'`, and are not instances; they are taken as
hypotheses in the shape a caller that has just built them can supply, together with the equation
pinning the algebra map down. The comparison itself is a parameter pinned by its values, for the
same reason. -/
theorem isBaseChange_appTop_pullbackSections
    {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T} (H : IsPullback p k iX q)
    [IsAffine S] [IsAffine T] [Flat q] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    [Algebra Γ(X, ⊤) Γ(Y, ⊤)]
    (halg : ∀ r, algebraMap Γ(X, ⊤) Γ(Y, ⊤) r = (p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom r)
    [Module Γ(X, ⊤) Γ((Scheme.Modules.pullback p).obj F, ⊤)]
    [IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) Γ((Scheme.Modules.pullback p).obj F, ⊤)]
    (ρ : Γ(F, ⊤) →ₗ[Γ(X, ⊤)] Γ((Scheme.Modules.pullback p).obj F, ⊤))
    (hρ : ∀ a, ρ a = pullbackSectionsHom p F ⊤ ⊤ (le_preimage_top p ⊤) a) :
    IsBaseChange Γ(Y, ⊤) ρ := by
  let algAB : Algebra Γ(S, ⊤) Γ(T, ⊤) := baseAlgebra q
  let modAF : Module Γ(S, ⊤) Γ(F, ⊤) := baseModule iX F ⊤
  let modAG : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback p).obj F, ⊤) :=
    baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) ⊤
  let modBG : Module Γ(T, ⊤) Γ((Scheme.Modules.pullback p).obj F, ⊤) :=
    baseModule k ((Scheme.Modules.pullback p).obj F) ⊤
  have towerG : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ((Scheme.Modules.pullback p).obj F, ⊤) :=
    baseTower H ((Scheme.Modules.pullback p).obj F) ⊤
  obtain ⟨e, he⟩ := exists_linearEquiv_sections_baseChange H F
  let algAX : Algebra Γ(S, ⊤) Γ(X, ⊤) := baseAlgebra iX
  let algBY : Algebra Γ(T, ⊤) Γ(Y, ⊤) := baseAlgebra k
  let algAY : Algebra Γ(S, ⊤) Γ(Y, ⊤) := baseAlgebra (p ≫ iX)
  have towerAXY : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(Y, ⊤) :=
    Stacks.FlatSectionsDescent.isScalarTower_of_smul_eq (algebraMap Γ(X, ⊤) Γ(Y, ⊤))
      (fun b m => by rw [Algebra.smul_def, smul_eq_mul])
      (((p ≫ iX).appLE ⊤ ⊤ (le_preimage_top (p ≫ iX) ⊤)).hom) (fun _ _ => rfl)
      (fun a => by rw [halg]; exact appLE_comp_base iX p ⊤ a)
  have towerATY : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, ⊤) :=
    Stacks.FlatSectionsDescent.isScalarTower_of_smul_eq
      (k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom (fun _ _ => rfl)
      (((p ≫ iX).appLE ⊤ ⊤ (le_preimage_top (p ≫ iX) ⊤)).hom) (fun _ _ => rfl)
      (sectionsSquare_comm H ⊤)
  have towerAXF : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) :=
    Stacks.FlatSectionsDescent.isScalarTower_of_smul_eq (RingHom.id _) (fun _ _ => rfl)
      ((iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom) (fun _ _ => rfl) (fun _ => rfl)
  have hUST : (⊤ : T.Opens) ≤ q ⁻¹ᵁ (⊤ : S.Opens) := le_preimage_top q ⊤
  have hpo : Algebra.IsPushout Γ(S, ⊤) Γ(T, ⊤) Γ(X, ⊤) Γ(Y, ⊤) :=
    algebraIsPushout_sections H ⊤ ⊤ hUST (le_preimage_top iX ⊤) (by simp)
      (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hUST
        (le_preimage_top iX ⊤) (by simp) (isAffineOpen_top S) (isAffineOpen_top T)
        (by simpa using isCompact_univ (X := X)) (by simpa using isQuasiSeparated_univ (α := X)))
      le_rfl (le_preimage_top k _) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      halg
  let can := Algebra.IsPushout.cancelBaseChange Γ(S, ⊤) Γ(T, ⊤) Γ(X, ⊤) Γ(Y, ⊤) Γ(F, ⊤)
  have he' : ∀ x, e x = (ρ.liftBaseChange Γ(Y, ⊤)) (can.symm x) := by
    intro x
    induction x with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul b m =>
        rw [he b m, Algebra.IsPushout.cancelBaseChange_symm_tmul,
          LinearMap.liftBaseChange_tmul, hρ]
        rfl
  have hbij : Function.Bijective (ρ.liftBaseChange Γ(Y, ⊤)) := by
    have key : ∀ y, (ρ.liftBaseChange Γ(Y, ⊤)) y = e (can y) := by
      intro y
      rw [he' (can y), can.symm_apply_apply]
    rw [show ((ρ.liftBaseChange Γ(Y, ⊤)) : _ → _) = (e : _ → _) ∘ can from funext key]
    exact e.bijective.comp can.bijective
  exact Stacks.FlatSectionsDescent.isBaseChange_of_bijective_liftBaseChange ρ hbij

/-- **Tag 02KH in degree zero for a quasi-coherent module, along a flat ring map.** For a
quasi-compact, quasi-separated scheme `X` over `A`, a flat ring map `φ : A →+* B` and a
quasi-coherent `𝒪_X`-module `F`, the canonical map

  `Γ(X, F) ⊗_{Γ(X, 𝒪_X)} Γ(X_B, 𝒪_{X_B}) ⟶ Γ(X_B, F_B)`

is an isomorphism. -/
theorem isBaseChange_appTop_pullbackSections_of_flat
    {A B : Type u} [CommRing A] [CommRing B] {φ : A →+* B} (hφ : φ.Flat)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    [Algebra Γ(X, ⊤) Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤)]
    (halg : ∀ r, algebraMap Γ(X, ⊤)
        Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤) r =
      ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))).appLE ⊤ ⊤
        (le_preimage_top _ ⊤)).hom r)
    [Module Γ(X, ⊤) Γ((Scheme.Modules.pullback
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj F, ⊤)]
    [IsScalarTower Γ(X, ⊤) Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤)
      Γ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj F, ⊤)]
    (ρ : Γ(F, ⊤) →ₗ[Γ(X, ⊤)] Γ((Scheme.Modules.pullback
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj F, ⊤))
    (hρ : ∀ a, ρ a =
      pullbackSectionsHom (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))) F ⊤ ⊤
        (le_preimage_top _ ⊤) a) :
    IsBaseChange Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤) ρ := by
  have hq : Flat (Spec.map (CommRingCat.ofHom φ)) := Flat.SpecMap_iff.mpr hφ
  exact isBaseChange_appTop_pullbackSections
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom φ))) F halg ρ hρ

end Stacks.AlgebraicGeometry.SectionsBaseChange

end
