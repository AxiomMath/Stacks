module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.AffineDeRham
public import StacksFrontier.AlgebraicGeometry.FormsTrace.AffinePullback
public import StacksFrontier.AlgebraicGeometry.FormsTrace.FiniteTrace
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.Charts
public import StacksFrontier.RingTheory.FormsTrace.Defs
public import StacksFrontier.RingTheory.FormsTrace.Basic
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# Gluing maps on forms from a basis of affine opens

Let `f : Y ⟶ X` be an affine morphism of schemes and let `W : ι → X.Opens` be a family of affine
opens of `X` whose range is a basis of the topology. A family of `Γ(X, W i)`-linear maps

`Θ_i^p : Ω^p_{Γ(Y, f⁻¹W i)} → Ω^p_{Γ(X, W i)}`

on the absolute forms of the rings of sections, compatible with the pull-backs of forms along the
restriction maps (`AlgebraicGeometry.Scheme.Hom.IsRestrictionCompatible`), glues to a morphism of
`𝒪_X`-modules `f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` whose sections over each `W i` are `Θ_i^p`, read
through `AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv` (Stacks 009U for the gluing). The
properties of Stacks, Lemma 0FLB and Proposition 0FLC pass from the `Θ_i` to the glued maps.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsRestrictionCompatible`: the compatibility of the family.
* `AlgebraicGeometry.Scheme.Hom.formsMapOfBasis`: the glued map.

## Main results

* `AlgebraicGeometry.Scheme.Hom.absoluteFormsSectionsEquiv_formsMapOfBasis_app`: its sections
  over `W i` are `Θ_i`; `eq_formsMapOfBasis` and `formsMap_ext_of_isBasis`: uniqueness.
* `AlgebraicGeometry.Scheme.Hom.formsMapOfBasis_deRhamComplex_d`: compatibility with `d`.
* `AlgebraicGeometry.Scheme.Hom.formsMapOfBasis_smul_absoluteFormsPullback`:
  `Θ(b · f^*ω) = Trace_f(b) · ω`.
* `AlgebraicGeometry.Scheme.Hom.formsMapOfBasis_mul_absoluteFormsPullback`:
  `Θ(f^*ω ∧ η) = ω ∧ Θ(η)`.
* `AlgebraicGeometry.Scheme.Hom.absoluteFormsSectionsEquiv_absoluteFormsPullback_app`: the
  pull-back of forms on an affine chart `(U, f⁻¹U)` is `Stacks.FormsTrace.formsMap`.

## Implementation notes

Sections of `f_*Ω^p_{Y/ℤ}`, of `Ω^p_{Y/ℤ}` over `f⁻¹U` and of the terms of the de Rham complex
agree definitionally, but their module and additive structures come in several spellings whose
unification is very expensive (maximum recursion depth). The proofs therefore never ask Lean to
identify two such spellings inside a large term: every statement is stated in one spelling, the
transitions are made by `rfl` lemmas on variables, and equalities are chained with `Eq.trans` and
`congrArg` or `rw` with fully applied lemmas.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Stacks.FormsTrace

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The map `Γ(Ω^p_Y, f⁻¹U) → Γ(Ω^p_X, U)` induced by a map
`Θ : Ω^p_{Γ(Y, f⁻¹U)} → Ω^p_{Γ(X, U)}` of absolute forms. -/
def formsSectionsFun {U : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U)) (p : ℕ)
    (Θ : letI := (f.app U).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ U)]^p Ω[Γ(Y, f ⁻¹ᵁ U)⁄ℤ] →ₗ[Γ(X, U)] ⋀[Γ(X, U)]^p Ω[Γ(X, U)⁄ℤ])
    (m : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) : Γ(absoluteDifferentialForms X p, U) :=
  (absoluteFormsSectionsEquiv X hU p).symm (Θ (absoluteFormsSectionsEquiv Y hV p m))

/-- `formsSectionsFun` is additive. -/
theorem formsSectionsFun_add {U : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U))
    (p : ℕ) (Θ : letI := (f.app U).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ U)]^p Ω[Γ(Y, f ⁻¹ᵁ U)⁄ℤ] →ₗ[Γ(X, U)] ⋀[Γ(X, U)]^p Ω[Γ(X, U)⁄ℤ])
    (m m' : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    formsSectionsFun f hU hV p Θ (m + m') =
      formsSectionsFun f hU hV p Θ m + formsSectionsFun f hU hV p Θ m' := by
  let := (f.app U).hom.toAlgebra
  have h1 := (absoluteFormsSectionsEquiv Y hV p).map_add m m'
  have h2 := Θ.map_add (absoluteFormsSectionsEquiv Y hV p m) (absoluteFormsSectionsEquiv Y hV p m')
  have h3 := (absoluteFormsSectionsEquiv X hU p).symm.map_add
    (Θ (absoluteFormsSectionsEquiv Y hV p m)) (Θ (absoluteFormsSectionsEquiv Y hV p m'))
  exact ((congrArg (fun z => (absoluteFormsSectionsEquiv X hU p).symm (Θ z)) h1).trans
    (congrArg (absoluteFormsSectionsEquiv X hU p).symm h2)).trans h3

/-- `formsSectionsFun` is semilinear along `f^♯`. -/
theorem formsSectionsFun_smul {U : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U))
    (p : ℕ) (Θ : letI := (f.app U).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ U)]^p Ω[Γ(Y, f ⁻¹ᵁ U)⁄ℤ] →ₗ[Γ(X, U)] ⋀[Γ(X, U)]^p Ω[Γ(X, U)⁄ℤ])
    (a : Γ(X, U)) (m : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    formsSectionsFun f hU hV p Θ ((f.app U).hom a • m) = a • formsSectionsFun f hU hV p Θ m := by
  have key : Θ (absoluteFormsSectionsEquiv Y hV p ((f.app U).hom a • m)) =
      a • Θ (absoluteFormsSectionsEquiv Y hV p m) := by
    let := (f.app U).hom.toAlgebra
    rw [map_smul (absoluteFormsSectionsEquiv Y hV p)]
    exact (congrArg Θ (algebraMap_smul _ a _)).trans (map_smul Θ a _)
  unfold formsSectionsFun
  rw [key, map_smul]

/-- The morphism of modules of sections over an affine open `U` (with `f⁻¹U` affine) induced by a
`Γ(X, U)`-linear map `Θ : Ω^p_{Γ(Y, f⁻¹U)} → Ω^p_{Γ(X, U)}` of absolute forms. -/
def formsSectionsMap {U : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U)) (p : ℕ)
    (Θ : letI := (f.app U).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ U)]^p Ω[Γ(Y, f ⁻¹ᵁ U)⁄ℤ] →ₗ[Γ(X, U)] ⋀[Γ(X, U)]^p Ω[Γ(X, U)⁄ℤ]) :
    ((Scheme.Modules.pushforward f).obj (absoluteDifferentialForms Y p)).val.obj (op U) ⟶
      (absoluteDifferentialForms X p).val.obj (op U) := by
  change ModuleCat.of Γ(X, U)
      Γ((Scheme.Modules.pushforward f).obj (absoluteDifferentialForms Y p), U) ⟶
    ModuleCat.of Γ(X, U) Γ(absoluteDifferentialForms X p, U)
  exact ModuleCat.ofHom
    { toFun := fun m => formsSectionsFun f hU hV p Θ m
      map_add' := fun m m' => formsSectionsFun_add f hU hV p Θ m m'
      map_smul' := fun a m => formsSectionsFun_smul f hU hV p Θ a m }

/-- `formsSectionsMap` on a section, through `ConcreteCategory.hom`. -/
private theorem formsSectionsMap_apply' {U : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen (f ⁻¹ᵁ U))
    (p : ℕ) (Θ : letI := (f.app U).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ U)]^p Ω[Γ(Y, f ⁻¹ᵁ U)⁄ℤ] →ₗ[Γ(X, U)] ⋀[Γ(X, U)]^p Ω[Γ(X, U)⁄ℤ])
    (m : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    ConcreteCategory.hom (formsSectionsMap f hU hV p Θ) m = formsSectionsFun f hU hV p Θ m :=
  rfl

/-- `formsSectionsMap` on a section. -/
theorem formsSectionsMap_apply {U : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U))
    (p : ℕ) (Θ : letI := (f.app U).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ U)]^p Ω[Γ(Y, f ⁻¹ᵁ U)⁄ℤ] →ₗ[Γ(X, U)] ⋀[Γ(X, U)]^p Ω[Γ(X, U)⁄ℤ])
    (m : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    (formsSectionsMap f hU hV p Θ).hom m = formsSectionsFun f hU hV p Θ m :=
  rfl

section Glue

/-- Restriction in `f_*Ω^p_{Y/ℤ}` is restriction in `Ω^p_{Y/ℤ}` along the preimages. -/
private theorem pushforward_forms_map_apply {U U' : X.Opens} (h : U' ≤ U) (p : ℕ)
    (s : ((Scheme.Modules.pushforward f).obj (absoluteDifferentialForms Y p)).val.obj (op U)) :
    (((Scheme.Modules.pushforward f).obj (absoluteDifferentialForms Y p)).val.map
        (homOfLE h).op).hom s =
      (absoluteDifferentialForms Y p).presheaf.map (homOfLE (f.preimage_mono h)).op s :=
  rfl

/-- Restriction of a sheaf of modules on sections, in the two spellings. -/
private theorem modules_val_map_apply {Z : Scheme.{u}} (M : Z.Modules) {U U' : Z.Opens} (h : U' ≤ U)
    (s : M.val.obj (op U)) :
    (M.val.map (homOfLE h).op).hom s = M.presheaf.map (homOfLE h).op s :=
  rfl

/-- `AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv_restrict_kaehlerMapₛₗ`, read on the
form attached to `y`: restricting the form whose identification is `y` gives the form whose
identification is the pull-back of `y`. -/
theorem absoluteFormsSectionsEquiv_restrict_symm {Z : Scheme.{u}} {V V' : Z.Opens}
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) (p : ℕ)
    (y : ⋀[Γ(Z, V)]^p Ω[Γ(Z, V)⁄ℤ]) :
    letI := Z.restrictAlgebra h
    absoluteFormsSectionsEquiv Z hV' p ((absoluteDifferentialForms Z p).presheaf.map
        (homOfLE h).op ((absoluteFormsSectionsEquiv Z hV p).symm y)) =
      formsMap Γ(Z, V) Γ(Z, V') p y := by
  let := Z.restrictAlgebra h
  have := absoluteFormsSectionsEquiv_restrict_kaehlerMapₛₗ hV hV' h p
    ((absoluteFormsSectionsEquiv Z hV p).symm y)
  rwa [LinearEquiv.apply_symm_apply] at this

/-- The two spellings of the sections of a morphism of sheaves of modules. -/
private theorem modules_hom_val_app_apply {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N)
    (U : Z.Opens)
    (s : M.val.obj (op U)) : (φ.val.app (op U)).hom s = φ.app U s :=
  rfl

/-- **The de Rham differential of `Ω^•_{Z/ℤ}` commutes with restriction**, on sections of the
sheaves of absolute forms. -/
theorem deRhamComplex_d_restrict {Z : Scheme.{u}} {V V' : Z.Opens} (h : V' ≤ V) (p : ℕ)
    (x : Γ(absoluteDifferentialForms Z p, V)) :
    (Z.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V')
        ((absoluteDifferentialForms Z p).presheaf.map (homOfLE h).op x) =
      (absoluteDifferentialForms Z ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h).op
        ((Z.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op V) x) :=
  PresheafOfModules.naturality_apply (Z.toSpecZ.deRhamComplex.d p (p + 1)).val (homOfLE h).op x

/-- A morphism `f_*M ⟶ N` commutes with restriction, the restriction of `f_*M` being the one of
`M` along the preimages. -/
theorem pushforward_hom_app_restrict {M : Y.Modules} {N : X.Modules}
    (φ : (Scheme.Modules.pushforward f).obj M ⟶ N) {U U' : X.Opens} (h : U' ≤ U)
    (x : Γ(M, f ⁻¹ᵁ U)) :
    φ.app U' (M.presheaf.map (homOfLE (f.preimage_mono h)).op x) =
      N.presheaf.map (homOfLE h).op (φ.app U x) :=
  Stacks.Tag01VSPullbackTensor.homApp_presheaf_map φ (homOfLE h) x

/-- Restricting along the identity of an open does nothing. -/
private theorem modules_presheaf_map_le_rfl {Z : Scheme.{u}} (M : Z.Modules) {V : Z.Opens}
    (h : V ≤ V) (s : Γ(M, V)) : M.presheaf.map (homOfLE h).op s = s := by
  rw [show homOfLE h = 𝟙 V from Subsingleton.elim _ _, op_id, M.presheaf.map_id]
  rfl

/-- **The pull-back of absolute forms over `U` and `f⁻¹U` is `formsMap`**: for affine `U` and
`f⁻¹U`, the identifications of sections with forms carry `f^* : Γ(Ω^p_{X/ℤ}, U) →
Γ(Ω^p_{Y/ℤ}, f⁻¹U)` to `Stacks.FormsTrace.formsMap` along `f^♯ = f.app U`. This is
`AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv_absoluteFormsPullback` for `V' = f⁻¹U`. -/
theorem absoluteFormsSectionsEquiv_absoluteFormsPullback_app {U : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U)) (p : ℕ)
    (ω : Γ(absoluteDifferentialForms X p, U)) :
    letI := (f.app U).hom.toAlgebra
    absoluteFormsSectionsEquiv Y hV p (f.absoluteFormsPullback p U ω) =
      formsMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U) p (absoluteFormsSectionsEquiv X hU p ω) := by
  have key := absoluteFormsSectionsEquiv_absoluteFormsPullback f hU hV (le_refl (f ⁻¹ᵁ U)) p ω
  have hres := modules_presheaf_map_le_rfl (absoluteDifferentialForms Y p) (le_refl (f ⁻¹ᵁ U))
    (f.absoluteFormsPullback p U ω)
  replace key : let := (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      absoluteFormsSectionsEquiv Y hV p (f.absoluteFormsPullback p U ω) =
        formsMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U) p (absoluteFormsSectionsEquiv X hU p ω) := by
    convert key using 2
    exact hres.symm
  have gen : ∀ φ : Γ(X, U) ⟶ Γ(Y, f ⁻¹ᵁ U), f.appLE U (f ⁻¹ᵁ U) le_rfl = φ →
      let := φ.hom.toAlgebra
      absoluteFormsSectionsEquiv Y hV p (f.absoluteFormsPullback p U ω) =
        formsMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U) p (absoluteFormsSectionsEquiv X hU p ω) := by
    intro φ hφ
    subst hφ
    exact key
  exact gen (f.app U) (Scheme.Hom.appLE_eq_app f)

/-- **Pulling back absolute forms commutes with restriction.** -/
private theorem absoluteFormsPullback_restrict {U U' : X.Opens} (h : U' ≤ U) (p : ℕ)
    (ω : Γ(absoluteDifferentialForms X p, U)) :
    (absoluteDifferentialForms Y p).presheaf.map (homOfLE (f.preimage_mono h)).op
        (f.absoluteFormsPullback p U ω) =
      f.absoluteFormsPullback p U'
        ((absoluteDifferentialForms X p).presheaf.map (homOfLE h).op ω) :=
  (relativeDifferentialFormsPullback_map f X.toSpecZ Y.toSpecZ (𝟙 _) (comp_toSpecZ f) p h ω).symm

/-- `Trace_f` commutes with restriction, read on functions. -/
theorem finiteTrace_restrict [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    {U U' : X.Opens} (h : U' ≤ U) (b : Γ(Y, f ⁻¹ᵁ U)) :
    (f.finiteTrace.app U' (Y.presheaf.map (homOfLE (f.preimage_mono h)).op b) : Γ(X, U')) =
      X.presheaf.map (homOfLE h).op (f.finiteTrace.app U b) :=
  pushforward_hom_app_restrict f f.finiteTrace h b

/-- The product of absolute forms, followed by the identification of the degree `q + p` taken in
`ℤ` with the degree `q + p` taken in `ℕ`, commutes with restriction. -/
theorem absoluteForms_castMul_restrict {Z : Scheme.{u}} (q p : ℕ) {V V' : Z.Opens} (h : V' ≤ V)
    (x : Γ(absoluteDifferentialForms Z q, V)) (y : Γ(absoluteDifferentialForms Z p, V)) :
    (absoluteDifferentialForms Z ((q + p : ℕ) : ℤ)).presheaf.map (homOfLE h).op
        ((eqToHom (congrArg (absoluteDifferentialForms Z) (Nat.cast_add q p).symm)).val.app (op V)
          (((absoluteDifferentialFormsAlgebra Z).mul q p).app (op V) x y)) =
      (eqToHom (congrArg (absoluteDifferentialForms Z) (Nat.cast_add q p).symm)).val.app (op V')
        (((absoluteDifferentialFormsAlgebra Z).mul q p).app (op V')
          ((absoluteDifferentialForms Z q).presheaf.map (homOfLE h).op x)
          ((absoluteDifferentialForms Z p).presheaf.map (homOfLE h).op y)) := by
  refine (Stacks.Tag01VSPullbackTensor.homApp_presheaf_map
    (eqToHom (congrArg (absoluteDifferentialForms Z) (Nat.cast_add q p).symm)) (homOfLE h)
      _).symm.trans ?_
  exact congrArg _ (((absoluteDifferentialFormsAlgebra Z).mul q p).naturality (homOfLE h).op x y)

/-- A section `Φ x` of `Ω^n_{X/ℤ}` over `U` is determined by its restrictions to the members of a
basis, where the restriction of `Φ x` is computed through `f_*`. -/
private theorem app_eq_of_restrict_eq {ι : Type*} {W : ι → X.Opens}
    (hB : Opens.IsBasis (Set.range W)) {n : ℤ}
    (Φ : (Scheme.Modules.pushforward f).obj (absoluteDifferentialForms Y n) ⟶
      absoluteDifferentialForms X n) {U : X.Opens} (x : Γ(absoluteDifferentialForms Y n, f ⁻¹ᵁ U))
    (z : Γ(absoluteDifferentialForms X n, U))
    (h : ∀ (a : ι) (hle : W a ≤ U),
      Φ.app (W a) ((absoluteDifferentialForms Y n).presheaf.map
          (homOfLE (f.preimage_mono hle)).op x) =
        (absoluteDifferentialForms X n).presheaf.map (homOfLE hle).op z) :
    Φ.app U x = z :=
  Stacks.BasisRestriction.moduleSheafSection_ext_onBasis (absoluteDifferentialForms X n) W hB _ _
    fun a hle => (pushforward_hom_app_restrict f Φ hle x).symm.trans (h a hle)

variable [IsAffineHom f] {ι : Type*} (W : ι → X.Opens) (hW : ∀ i, IsAffineOpen (W i))

/-- **Compatibility of a family of ring-level maps on forms with restriction**: for `W j ≤ W i`,
`Θ_j ∘ (Ω^p_{B_i} → Ω^p_{B_j}) = (Ω^p_{A_i} → Ω^p_{A_j}) ∘ Θ_i`, where `A_i = Γ(X, W i)`,
`B_i = Γ(Y, f⁻¹(W i))` and the maps on forms are the pull-backs along the restriction maps. -/
def IsRestrictionCompatible
    (Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ]) :
    Prop :=
  ∀ (i j : ι) (h : W j ≤ W i) (p : ℕ) (η : ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ]),
    letI := X.restrictAlgebra h
    letI := Y.restrictAlgebra (f.preimage_mono h)
    Θ j p (formsMap Γ(Y, f ⁻¹ᵁ W i) Γ(Y, f ⁻¹ᵁ W j) p η) =
      formsMap Γ(X, W i) Γ(X, W j) p (Θ i p η)

variable {W} in
/-- The section maps attached to a restriction-compatible family commute with the restriction
maps between the `W i`. -/
theorem formsSectionsMap_isCompatibleOnBasis
    {Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ]}
    (hΘ : IsRestrictionCompatible f W Θ) (p : ℕ) :
    Stacks.BasisRestriction.IsCompatibleOnBasis
      ((Scheme.Modules.pushforward f).obj (absoluteDifferentialForms Y p))
      (absoluteDifferentialForms X p) W
      (fun i => formsSectionsMap f (hW i) ((hW i).preimage f) p (Θ i p)) := by
  intro i j h s
  beta_reduce
  have e1 := pushforward_forms_map_apply f h p s
  have e2 := formsSectionsMap_apply' f (hW j) ((hW j).preimage f) p (Θ j p)
    ((absoluteDifferentialForms Y p).presheaf.map (homOfLE (f.preimage_mono h)).op s)
  have e3 := formsSectionsMap_apply' f (hW i) ((hW i).preimage f) p (Θ i p) s
  have e4 := modules_val_map_apply (absoluteDifferentialForms X p) h
    (formsSectionsFun f (hW i) ((hW i).preimage f) p (Θ i p) s)
  have key : formsSectionsFun f (hW j) ((hW j).preimage f) p (Θ j p)
      ((absoluteDifferentialForms Y p).presheaf.map (homOfLE (f.preimage_mono h)).op s) =
    (absoluteDifferentialForms X p).presheaf.map (homOfLE h).op
      (formsSectionsFun f (hW i) ((hW i).preimage f) p (Θ i p) s) := by
    let := X.restrictAlgebra h
    let := Y.restrictAlgebra (f.preimage_mono h)
    have hY := absoluteFormsSectionsEquiv_restrict_kaehlerMapₛₗ ((hW i).preimage f)
      ((hW j).preimage f) (f.preimage_mono h) p s
    have hX := absoluteFormsSectionsEquiv_restrict_symm (hW i) (hW j) h p
      (Θ i p (absoluteFormsSectionsEquiv Y ((hW i).preimage f) p s))
    have hc := hΘ i j h p (absoluteFormsSectionsEquiv Y ((hW i).preimage f) p s)
    apply (absoluteFormsSectionsEquiv X (hW j) p).injective
    unfold formsSectionsFun
    rwa [LinearEquiv.apply_symm_apply, hY, hX]
  refine ((congrArg (ConcreteCategory.hom (formsSectionsMap f (hW j) ((hW j).preimage f) p
    (Θ j p))) e1).trans e2).trans (key.trans ?_)
  exact e4.symm.trans (congrArg _ e3.symm)


variable {W} in
/-- **The glued map on forms** `f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}`: the morphism of sheaves of
`𝒪_X`-modules whose sections over each `W i` are `Θ i p`, read through
`AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv` on both sides. -/
def formsMapOfBasis
    (Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ])
    (hΘ : IsRestrictionCompatible f W Θ) (hB : Opens.IsBasis (Set.range W)) (p : ℕ) :
    (Scheme.Modules.pushforward f).obj (absoluteDifferentialForms Y p) ⟶
      absoluteDifferentialForms X p :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis _ _ W
    (fun i => formsSectionsMap f (hW i) ((hW i).preimage f) p (Θ i p)) hB
    (formsSectionsMap_isCompatibleOnBasis f hW hΘ p)

variable {W} in
/-- The components of `formsMapOfBasis` on the `W i`. -/
theorem formsMapOfBasis_val_app
    (Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ])
    (hΘ : IsRestrictionCompatible f W Θ) (hB : Opens.IsBasis (Set.range W)) (p : ℕ) (i : ι) :
    (formsMapOfBasis f hW Θ hΘ hB p).val.app (op (W i)) =
      formsSectionsMap f (hW i) ((hW i).preimage f) p (Θ i p) :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app _ _ _ _ _ _ i

variable {W} in
/-- **`formsMapOfBasis` on the `W i`**: through the identifications of sections with forms, the
sections of the glued map over `W i` are `Θ i p`. -/
theorem absoluteFormsSectionsEquiv_formsMapOfBasis_app
    (Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ])
    (hΘ : IsRestrictionCompatible f W Θ) (hB : Opens.IsBasis (Set.range W)) (p : ℕ) (i : ι)
    (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ W i)) :
    absoluteFormsSectionsEquiv X (hW i) p ((formsMapOfBasis f hW Θ hΘ hB p).app (W i) η) =
      Θ i p (absoluteFormsSectionsEquiv Y ((hW i).preimage f) p η) := by
  have h1 : (formsMapOfBasis f hW Θ hΘ hB p).app (W i) η =
      formsSectionsFun f (hW i) ((hW i).preimage f) p (Θ i p) η :=
    (congrArg (fun φ : ((Scheme.Modules.pushforward f).obj
        (absoluteDifferentialForms Y p)).val.obj (op (W i)) ⟶
          (absoluteDifferentialForms X p).val.obj (op (W i)) => ConcreteCategory.hom φ η)
      (formsMapOfBasis_val_app f hW Θ hΘ hB p i)).trans
      (formsSectionsMap_apply' f (hW i) ((hW i).preimage f) p (Θ i p) η)
  rw [h1]
  exact LinearEquiv.apply_symm_apply _ _

variable {W} in
/-- **Uniqueness of the glued map**: a morphism `f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` whose sections over
every `W i` are `Θ i p`, read through the identifications of sections with forms, is
`formsMapOfBasis`. -/
theorem eq_formsMapOfBasis
    (Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ])
    (hΘ : IsRestrictionCompatible f W Θ) (hB : Opens.IsBasis (Set.range W)) (p : ℕ)
    (E : (Scheme.Modules.pushforward f).obj (absoluteDifferentialForms Y p) ⟶
      absoluteDifferentialForms X p)
    (hE : ∀ (i : ι) (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ W i)),
      absoluteFormsSectionsEquiv X (hW i) p (E.app (W i) η) =
        Θ i p (absoluteFormsSectionsEquiv Y ((hW i).preimage f) p η)) :
    E = formsMapOfBasis f hW Θ hΘ hB p := by
  refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _ W hB _ _ fun i => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun η => ?_)
  rw [modules_hom_val_app_apply, modules_hom_val_app_apply]
  exact (absoluteFormsSectionsEquiv X (hW i) p).injective
    ((hE i η).trans (absoluteFormsSectionsEquiv_formsMapOfBasis_app f hW Θ hΘ hB p i η).symm)

omit [IsAffineHom f] in
variable {W} in
/-- **Two morphisms `f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` with the same sections over every `W i` are
equal.** -/
theorem formsMap_ext_of_isBasis (hB : Opens.IsBasis (Set.range W)) (p : ℕ)
    (E₁ E₂ : (Scheme.Modules.pushforward f).obj (absoluteDifferentialForms Y p) ⟶
      absoluteDifferentialForms X p)
    (h : ∀ (i : ι) (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ W i)),
      E₁.app (W i) η = E₂.app (W i) η) :
    E₁ = E₂ :=
  Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _ W hB _ _ fun i =>
    ModuleCat.hom_ext (LinearMap.ext fun η => h i η)

variable {W} in
/-- The glued maps commute with `d` on the sections over each `W i`, when every `Θ i` does. -/
theorem formsMapOfBasis_deRhamComplex_d_basis
    (Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ])
    (hΘ : IsRestrictionCompatible f W Θ) (hB : Opens.IsBasis (Set.range W))
    (hd : ∀ i, letI := (f.app (W i)).hom.toAlgebra
      Stacks.FormsTrace.CommutesWithD Γ(X, W i) Γ(Y, f ⁻¹ᵁ W i) (Θ i))
    (p : ℕ) (i : ι) (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ W i)) :
    (formsMapOfBasis f hW Θ hΘ hB (p + 1)).app (W i)
        ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op (f ⁻¹ᵁ W i)) η) =
      (X.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op (W i))
        ((formsMapOfBasis f hW Θ hΘ hB p).app (W i) η) := by
  apply (absoluteFormsSectionsEquiv X (hW i) (p + 1)).injective
  have h1 := absoluteFormsSectionsEquiv_formsMapOfBasis_app f hW Θ hΘ hB (p + 1) i
    ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op (f ⁻¹ᵁ W i)) η)
  have h2 := absoluteFormsSectionsEquiv_deRhamComplex_d Y ((hW i).preimage f) p η
  have h3 := hd i p (absoluteFormsSectionsEquiv Y ((hW i).preimage f) p η)
  have h4 := absoluteFormsSectionsEquiv_formsMapOfBasis_app f hW Θ hΘ hB p i η
  have h5 := absoluteFormsSectionsEquiv_deRhamComplex_d X (hW i) p
    ((formsMapOfBasis f hW Θ hΘ hB p).app (W i) η)
  rw [h1, h2, h3, h5, h4]

variable {W} in
/-- **The glued maps form a map of de Rham complexes** `f_*Ω^•_{Y/ℤ} → Ω^•_{X/ℤ}`, when every
`Θ i` commutes with the de Rham differentials: on sections over any open `U` of `X`,
`Θ^{p+1}(d η) = d(Θ^p η)`. -/
theorem formsMapOfBasis_deRhamComplex_d
    (Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ])
    (hΘ : IsRestrictionCompatible f W Θ) (hB : Opens.IsBasis (Set.range W))
    (hd : ∀ i, letI := (f.app (W i)).hom.toAlgebra
      Stacks.FormsTrace.CommutesWithD Γ(X, W i) Γ(Y, f ⁻¹ᵁ W i) (Θ i))
    (p : ℕ) (U : X.Opens) (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    (formsMapOfBasis f hW Θ hΘ hB (p + 1)).app U
        ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op (f ⁻¹ᵁ U)) η) =
      (X.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op U)
        ((formsMapOfBasis f hW Θ hΘ hB p).app U η) := by
  refine app_eq_of_restrict_eq f hB _ _ _ fun a hle => ?_
  exact (congrArg ((formsMapOfBasis f hW Θ hΘ hB (p + 1)).app (W a))
        (deRhamComplex_d_restrict (f.preimage_mono hle) p η).symm).trans
      ((formsMapOfBasis_deRhamComplex_d_basis f hW Θ hΘ hB hd p a _).trans
      ((congrArg ((X.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op (W a)))
        (pushforward_hom_app_restrict f (formsMapOfBasis f hW Θ hΘ hB p) hle η)).trans
      (deRhamComplex_d_restrict hle p _)))

variable {W} in
/-- Property (1) of Stacks, Lemma 0FLB for the glued maps, on the sections over each `W i`. -/
theorem formsMapOfBasis_smul_absoluteFormsPullback_basis
    (Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ])
    (hΘ : IsRestrictionCompatible f W Θ) (hB : Opens.IsBasis (Set.range W)) (i : ι)
    [hfin : letI := (f.app (W i)).hom.toAlgebra; Module.Finite Γ(X, W i) Γ(Y, f ⁻¹ᵁ W i)]
    [hproj : letI := (f.app (W i)).hom.toAlgebra; Module.Projective Γ(X, W i) Γ(Y, f ⁻¹ᵁ W i)]
    (hT : letI := (f.app (W i)).hom.toAlgebra
      IsFormsTrace Γ(X, W i) Γ(Y, f ⁻¹ᵁ W i) (Θ i))
    (p : ℕ) (b : Γ(Y, f ⁻¹ᵁ W i)) (ω : Γ(absoluteDifferentialForms X p, W i)) :
    letI := (f.app (W i)).hom.toAlgebra
    (formsMapOfBasis f hW Θ hΘ hB p).app (W i) (b • f.absoluteFormsPullback p (W i) ω) =
      trace Γ(X, W i) Γ(Y, f ⁻¹ᵁ W i) b • ω := by
  let := (f.app (W i)).hom.toAlgebra
  apply (absoluteFormsSectionsEquiv X (hW i) p).injective
  rw [absoluteFormsSectionsEquiv_formsMapOfBasis_app, map_smul (absoluteFormsSectionsEquiv Y _ p),
    absoluteFormsSectionsEquiv_absoluteFormsPullback_app f (hW i) ((hW i).preimage f), hT p b,
    map_smul]

variable {W} in
/-- **Property (1) of Stacks, Lemma 0FLB for the glued maps**: if every `Θ i` satisfies
`Θ(b · f^*ω) = Trace(b) · ω` (`Stacks.FormsTrace.IsFormsTrace`), then so does the glued map, on
the sections over every open `U` of `X`: `Θ^p(b · f^*ω) = Trace_f(b) · ω`. -/
theorem formsMapOfBasis_smul_absoluteFormsPullback [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f]
    (Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ])
    (hΘ : IsRestrictionCompatible f W Θ) (hB : Opens.IsBasis (Set.range W))
    (hT : ∀ i, letI := (f.app (W i)).hom.toAlgebra
      ∀ [Module.Finite Γ(X, W i) Γ(Y, f ⁻¹ᵁ W i)] [Module.Projective Γ(X, W i) Γ(Y, f ⁻¹ᵁ W i)],
        IsFormsTrace Γ(X, W i) Γ(Y, f ⁻¹ᵁ W i) (Θ i))
    (p : ℕ) (U : X.Opens) (b : Γ(Y, f ⁻¹ᵁ U)) (ω : Γ(absoluteDifferentialForms X p, U)) :
    (formsMapOfBasis f hW Θ hΘ hB p).app U (b • f.absoluteFormsPullback p U ω) =
      (show Γ(X, U) from f.finiteTrace.app U b) • ω := by
  refine app_eq_of_restrict_eq f hB _ _ _ fun a hle => ?_
  let := (f.app (W a)).hom.toAlgebra
  have := f.moduleFinite_app (W a) (hW a)
  have := f.moduleProjective_app (W a) (hW a)
  have hb := formsMapOfBasis_smul_absoluteFormsPullback_basis f hW Θ hΘ hB a (hT a) p
    (Y.presheaf.map (homOfLE (f.preimage_mono hle)).op b)
    ((absoluteDifferentialForms X p).presheaf.map (homOfLE hle).op ω)
  have htr := f.finiteTrace_app_of_isAffineOpen (W a) (hW a)
    (Y.presheaf.map (homOfLE (f.preimage_mono hle)).op b)
  rw [Scheme.Modules.map_smul, absoluteFormsPullback_restrict f hle, hb, Scheme.Modules.map_smul]
  dsimp only
  rw [← finiteTrace_restrict f hle, htr]

variable {W} in
/-- Wedge-linearity of the glued maps on the sections over each `W i`. -/
theorem formsMapOfBasis_mul_absoluteFormsPullback_basis
    (Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ])
    (hΘ : IsRestrictionCompatible f W Θ) (hB : Opens.IsBasis (Set.range W)) (i : ι)
    (hw : letI := (f.app (W i)).hom.toAlgebra
      IsWedgeLinear Γ(X, W i) Γ(Y, f ⁻¹ᵁ W i) (Θ i))
    (q p : ℕ) (ω : Γ(absoluteDifferentialForms X q, W i))
    (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ W i)) :
    (formsMapOfBasis f hW Θ hΘ hB (q + p)).app (W i)
        ((eqToHom (congrArg (absoluteDifferentialForms Y) (Nat.cast_add q p).symm)).val.app
          (op (f ⁻¹ᵁ W i)) (((absoluteDifferentialFormsAlgebra Y).mul q p).app (op (f ⁻¹ᵁ W i))
            (f.absoluteFormsPullback q (W i) ω) η)) =
      (eqToHom (congrArg (absoluteDifferentialForms X) (Nat.cast_add q p).symm)).val.app (op (W i))
        (((absoluteDifferentialFormsAlgebra X).mul q p).app (op (W i)) ω
          ((formsMapOfBasis f hW Θ hΘ hB p).app (W i) η)) := by
  let := (f.app (W i)).hom.toAlgebra
  apply (absoluteFormsSectionsEquiv X (hW i) (q + p)).injective
  refine (absoluteFormsSectionsEquiv_formsMapOfBasis_app f hW Θ hΘ hB (q + p) i _).trans ?_
  have h1 := absoluteFormsSectionsEquiv_mul Y ((hW i).preimage f) q p
    (f.absoluteFormsPullback q (W i) ω) η
  have h2 := absoluteFormsSectionsEquiv_mul X (hW i) q p ω
    ((formsMapOfBasis f hW Θ hΘ hB p).app (W i) η)
  have h3 := absoluteFormsSectionsEquiv_absoluteFormsPullback_app f (hW i) ((hW i).preimage f) q ω
  have h4 := absoluteFormsSectionsEquiv_formsMapOfBasis_app f hW Θ hΘ hB p i η
  have h5 := hw q p (absoluteFormsSectionsEquiv X (hW i) q ω)
    (absoluteFormsSectionsEquiv Y ((hW i).preimage f) p η)
  refine (congrArg (Θ i (q + p)) (h1.trans (congrArg (fun z => exteriorPower.wedgeMul q p z
    (absoluteFormsSectionsEquiv Y ((hW i).preimage f) p η)) h3))).trans ?_
  refine h5.trans ?_
  refine Eq.trans ?_ h2.symm
  exact congrArg (exteriorPower.wedgeMul q p (absoluteFormsSectionsEquiv X (hW i) q ω)) h4.symm

variable {W} in
/-- **The glued maps are linear over the forms of `X`** (Stacks, Proposition 0FLC (2)), when
every `Θ i` is: on the sections over any open `U` of `X`, `Θ^{q+p}(f^*ω ∧ η) = ω ∧ Θ^p(η)` for a
form `ω` of `X` over `U` and a form `η` of `Y` over `f⁻¹U`. The products are those of the graded
algebras `Ω^•_{·/ℤ}` in the degree `(q : ℤ) + p`, transported to the degree `((q + p : ℕ) : ℤ)`
by `eqToHom`, as in `AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv_mul`. -/
theorem formsMapOfBasis_mul_absoluteFormsPullback
    (Θ : ∀ (i : ι) (p : ℕ), letI := (f.app (W i)).hom.toAlgebra
      ⋀[Γ(Y, f ⁻¹ᵁ W i)]^p Ω[Γ(Y, f ⁻¹ᵁ W i)⁄ℤ] →ₗ[Γ(X, W i)] ⋀[Γ(X, W i)]^p Ω[Γ(X, W i)⁄ℤ])
    (hΘ : IsRestrictionCompatible f W Θ) (hB : Opens.IsBasis (Set.range W))
    (hw : ∀ i, letI := (f.app (W i)).hom.toAlgebra
      IsWedgeLinear Γ(X, W i) Γ(Y, f ⁻¹ᵁ W i) (Θ i))
    (q p : ℕ) (U : X.Opens) (ω : Γ(absoluteDifferentialForms X q, U))
    (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    (formsMapOfBasis f hW Θ hΘ hB (q + p)).app U
        ((eqToHom (congrArg (absoluteDifferentialForms Y) (Nat.cast_add q p).symm)).val.app
          (op (f ⁻¹ᵁ U)) (((absoluteDifferentialFormsAlgebra Y).mul q p).app (op (f ⁻¹ᵁ U))
            (f.absoluteFormsPullback q U ω) η)) =
      (eqToHom (congrArg (absoluteDifferentialForms X) (Nat.cast_add q p).symm)).val.app (op U)
        (((absoluteDifferentialFormsAlgebra X).mul q p).app (op U) ω
          ((formsMapOfBasis f hW Θ hΘ hB p).app U η)) := by
  refine app_eq_of_restrict_eq f hB _ _ _ fun a hle => ?_
  rw [absoluteForms_castMul_restrict, absoluteFormsPullback_restrict f hle,
    formsMapOfBasis_mul_absoluteFormsPullback_basis f hW Θ hΘ hB a (hw a),
    pushforward_hom_app_restrict f (formsMapOfBasis f hW Θ hΘ hB p) hle,
    absoluteForms_castMul_restrict]

end Glue

end AlgebraicGeometry.Scheme.Hom

end
