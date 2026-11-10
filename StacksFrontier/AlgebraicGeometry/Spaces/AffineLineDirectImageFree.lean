module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseTerminalChartIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalenceObstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatGlobalSectionsRingHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The direct image of the structure sheaf of the affine line is free

Let `S` be an affine scheme in a big fppf site, let `Y = h_S` be the algebraic space it
represents, let `X = h_{𝔸¹_S}` and let `f : X ⟶ Y` be the structure morphism. Then the direct
image `f_*𝒪_X` of the structure sheaf on the small étale site of `Y` is a free `𝒪_Y`-module of
countable rank:

`f_*𝒪_X ≅ 𝒪_Y^{⊕ ℕ}`.

This is the étale form of `Stacks.Duality.AffineLine.pushforwardStructureSheafIso`, the input of
[Stacks, Tag 0GEU] that `R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y)` is a product of copies of `𝒪_Y`, and so it
is the input of [Stacks, Tag 0GG3].

## Main results

* `AlgebraicGeometry.Space.nonempty_free_iso_of_basis` — a quasi-coherent module on an algebraic
  space with a terminal affine chart `V₀`, whose sections over `V₀` are a free module, is free.
* `AlgebraicGeometry.Space.affineSpaceGlobalSectionsBasis` — `Γ(𝔸ⁿ_T, 𝒪)` is free over `Γ(T, 𝒪)`
  for an affine scheme `T`, on the monomials.
* `AlgebraicGeometry.Space.nonempty_affineLineDirectImageFreeIso` — `f_*𝒪_X ≅ 𝒪_Y^{⊕ ℕ}`.

## Implementation notes

*Freeness is detected on the terminal chart.* A morphism of quasi-coherent modules on an
algebraic space with a terminal affine chart `V₀` is invertible as soon as it is bijective on the
sections over `V₀` (`AlgebraicGeometry.Space.isIso_of_bijective_val_app_isTerminal`, by
Descent, Proposition 03DX (2)), and the sections of `𝒪_Y^{⊕ I}` over an affine chart are the
finitely supported families (`AlgebraicGeometry.Space.bijective_freeSectionsMap_of_isAffine`). So
a basis of the sections over `V₀` produces the isomorphism.

*The sections of `f_*𝒪_X` over `V₀`.* They are the regular functions on the scheme `X ×_Y V₀`
(`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`), the structure map being pullback
along the projection (`AlgebraicGeometry.Space.fSharp_app_comp_pushforwardAlgebraSectionsIso`,
Stacks 03G8 part (2)); `V₀` being the identity chart, that scheme is `𝔸¹_S` over `S`.

## References

* [Stacks Project, Tag 0GEU](https://stacks.math.columbia.edu/tag/0GEU)
* [Stacks Project, Tag 0GG3](https://stacks.math.columbia.edu/tag/0GG3)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Transporting a basis along a ring isomorphism over the scalars -/

/-- A ring isomorphism `e : A ≃+* P` compatible with ring maps `φ : R → A` and `ψ : R → P` is
`R`-linear for the module structures they induce. -/
def linearEquivOfRingEquiv {R A P : Type*} [CommRing R] [CommRing A] [CommRing P]
    (φ : R →+* A) (ψ : R →+* P) (e : A ≃+* P) (he : ∀ r, e (φ r) = ψ r) :
    letI := Module.compHom A φ
    letI := Module.compHom P ψ
    A ≃ₗ[R] P :=
  letI := Module.compHom A φ
  letI := Module.compHom P ψ
  { e.toAddEquiv with
    map_smul' := fun r a => by
      change e (φ r * a) = ψ r * e a
      rw [map_mul, he] }

/-! ### Sections from a terminal object -/

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- The global section of a presheaf of modules determined by its value at a terminal object. -/
def sectionsOfIsTerminal (M : SheafOfModules.{u} R) {T : C} (hT : IsTerminal T)
    (x : M.val.obj (op T)) : M.sections :=
  PresheafOfModules.sectionsMk (fun X => M.val.map (hT.from X.unop).op x) (fun X Y g => by
    rw [← PresheafOfModules.map_comp_apply]
    exact PresheafOfModules.congr_map_apply M.val (Quiver.Hom.unop_inj (hT.hom_ext _ _)) x)

/-- The global section `sectionsOfIsTerminal M hT x` takes the value `x` at the terminal object
`T`. -/
theorem sectionsOfIsTerminal_val_self (M : SheafOfModules.{u} R) {T : C} (hT : IsTerminal T)
    (x : M.val.obj (op T)) : (sectionsOfIsTerminal M hT x).val (op T) = x := by
  change M.val.map (hT.from T).op x = x
  rw [show hT.from T = 𝟙 T from hT.hom_ext _ _, op_id, M.val.map_id]
  rfl

/-- The morphism `𝒪 ⟶ M` attached to a global section `s` sends `r` to `r • s`. -/
theorem unitHomEquiv_symm_val_app_apply [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (M : SheafOfModules.{u} R) (s : M.sections)
    (X : Cᵒᵖ) (r : R.obj.obj X) :
    (M.unitHomEquiv.symm s).val.app X r = r • (show M.val.obj X from s.val X) := by
  have h1 : (M.unitHomEquiv.symm s).val.app X (1 : R.obj.obj X) = s.val X :=
    congrArg (fun σ : M.sections => σ.val X) (M.unitHomEquiv.apply_symm_apply s)
  let one : (SheafOfModules.unit R).val.obj X := (1 : R.obj.obj X)
  have hr : (show (SheafOfModules.unit R).val.obj X from r) = r • one := (mul_one r).symm
  calc ((M.unitHomEquiv.symm s).val.app X).hom r
      = ((M.unitHomEquiv.symm s).val.app X).hom (r • one) := congrArg _ hr
    _ = r • ((M.unitHomEquiv.symm s).val.app X).hom one := map_smul _ _ _
    _ = r • (show M.val.obj X from s.val X) := congrArg (r • ·) h1


/-! ### A quasi-coherent module with free sections over a terminal affine chart is free -/

section FreeOfBasis

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A quasi-coherent module whose sections over a terminal affine chart are free is free.** Let
`Y` be an algebraic space with a terminal étale chart `V₀` whose scheme is affine, and let `M` be
a quasi-coherent `𝒪_Y`-module such that `M(V₀)` is a free `𝒪_Y(V₀)`-module with basis indexed by
`I`. Then `M ≅ 𝒪_Y^{⊕ I}`: the morphism `𝒪_Y^{⊕ I} ⟶ M` sending the `i`-th generator to the
global section extending the `i`-th basis vector is bijective on the sections over `V₀`. -/
theorem nonempty_free_iso_of_basis (Y : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    {V₀ : SmallEtale B S hS Y.1} (hV₀ : IsTerminal V₀) (hV₀aff : IsAffineChart B S hS Y.1 V₀)
    {I : Type u} (b : Module.Basis I (chartRing B S hS Y.1 Y.2 V₀) (M.val.obj (op V₀))) :
    Nonempty (SheafOfModules.free
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) I ≅
        M) := by
  let s : I → M.sections := fun i => sectionsOfIsTerminal M hV₀ (b i)
  let φ := M.freeHomEquiv.symm s
  have hcomp : (φ.val.app (op V₀)).hom ∘
        (Stacks.Sites.freeSectionsMap (R := Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O) I (op V₀)).hom =
      Finsupp.linearCombination (chartRing B S hS Y.1 Y.2 V₀) b := by
    funext c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c c' hc hc' =>
      simp only [Function.comp_apply, map_add] at hc hc' ⊢
      rw [hc, hc']
    | single i r =>
      rw [Function.comp_apply, Stacks.Sites.freeSectionsMap_single,
        Finsupp.linearCombination_single]
      have hφ : SheafOfModules.ιFree (R := Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O) i ≫ φ = M.unitHomEquiv.symm (s i) := by
        rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
      change ((SheafOfModules.ιFree (R := Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O) i ≫ φ).val.app (op V₀)).hom r = r • b i
      rw [hφ, unitHomEquiv_symm_val_app_apply]
      exact congrArg (r • ·) (sectionsOfIsTerminal_val_self M hV₀ (b i))
  have hbij : Function.Bijective (φ.val.app (op V₀)).hom := by
    refine (Function.Bijective.of_comp_iff _
      (bijective_freeSectionsMap_of_isAffine B S hS Y.1 Y.2 I V₀ hV₀aff)).1 ?_
    rw [hcomp, ← b.coe_repr_symm]
    exact b.repr.symm.bijective
  have : IsIso φ := isIso_of_bijective_val_app_isTerminal B S hS Y
    (isQuasicoherentOnSite_free B S hS Y.1 Y.2 I) hM φ hV₀ hV₀aff hbij
  exact ⟨asIso φ⟩

end FreeOfBasis

/-! ### The regular functions on affine space are free over the base -/

section AffineSpace

/-- **`Γ(𝔸ⁿ_T, 𝒪) = Γ(T, 𝒪)[x_i]`** for an affine scheme `T`: evaluation of polynomials at the
coordinate functions, along the structure morphism, is a ring isomorphism. -/
def affineSpaceGlobalSectionsRingEquiv (n : Type u) (T : Scheme.{u}) [IsAffine T] :
    MvPolynomial n Γ(T, ⊤) ≃+* Γ(𝔸(n; T), ⊤) :=
  RingEquiv.ofBijective
    (MvPolynomial.eval₂Hom (𝔸(n; T) ↘ T).appTop.hom (AffineSpace.coord T)) (by
      have h := AffineSpace.isoOfIsAffine_hom_appTop (n := n) (S := T)
      have h' : IsIso ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n Γ(T, ⊤)))).hom ≫
          CommRingCat.ofHom (MvPolynomial.eval₂Hom ((𝔸(n; T) ↘ T).appTop).hom
            (AffineSpace.coord T))) :=
        h ▸ inferInstanceAs (IsIso ((AffineSpace.isoOfIsAffine n T).hom.app ⊤))
      have : IsIso (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((𝔸(n; T) ↘ T).appTop).hom
          (AffineSpace.coord T))) :=
        IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n Γ(T, ⊤)))).hom _
      exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (MvPolynomial.eval₂Hom
        ((𝔸(n; T) ↘ T).appTop).hom (AffineSpace.coord T))))

/-- The isomorphism `affineSpaceGlobalSectionsRingEquiv` sends a constant polynomial `C r` to the
pullback of `r` along the structure morphism `𝔸ⁿ_T ⟶ T`. -/
theorem affineSpaceGlobalSectionsRingEquiv_C (n : Type u) (T : Scheme.{u}) [IsAffine T]
    (r : Γ(T, ⊤)) :
    affineSpaceGlobalSectionsRingEquiv n T (MvPolynomial.C r) = (𝔸(n; T) ↘ T).appTop r :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- **`Γ(𝔸ⁿ_T, 𝒪)` is a free `Γ(T, 𝒪)`-module, on the monomials**, for an affine scheme `T`,
the scalars acting through the structure morphism. -/
def affineSpaceGlobalSectionsBasis (n : Type u) (T : Scheme.{u}) [IsAffine T] :
    letI := Module.compHom Γ(𝔸(n; T), ⊤) (𝔸(n; T) ↘ T).appTop.hom
    Module.Basis (n →₀ ℕ) Γ(T, ⊤) Γ(𝔸(n; T), ⊤) :=
  letI := Module.compHom Γ(𝔸(n; T), ⊤) (𝔸(n; T) ↘ T).appTop.hom
  (MvPolynomial.basisMonomials n Γ(T, ⊤)).map
    { (affineSpaceGlobalSectionsRingEquiv n T).toAddEquiv with
      map_smul' := fun r q => by
        change affineSpaceGlobalSectionsRingEquiv n T (r • q) =
          (𝔸(n; T) ↘ T).appTop r * affineSpaceGlobalSectionsRingEquiv n T q
        rw [← MvPolynomial.C_mul', map_mul, affineSpaceGlobalSectionsRingEquiv_C] }

end AffineSpace

/-! ### The affine line over an affine base -/

section AffineLine

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsAffine S]

/-- The base `S`, as an object of the big fppf site over itself. -/
abbrev affineBase : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The scheme underlying `affineBase` is affine. -/
theorem isAffine_affineBase :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (affineBase B S hS)) :=
  inferInstanceAs (IsAffine S)

/-- The affine line `𝔸¹_S`, as an object of the big fppf site over `S`. -/
abbrev affineLineTotal : BigFppfOver B S hS :=
  BigFppfOver.affineSpace B S hS 1 (affineBase B S hS)

/-- The structure morphism `𝔸¹_S ⟶ S`, as a morphism of the big fppf site over `S`. -/
abbrev affineLineProj : affineLineTotal B S hS ⟶ affineBase B S hS :=
  BigFppfOver.affineSpaceProj B S hS 1 (affineBase B S hS)

/-- The algebraic space `Y = h_S`. -/
abbrev affineBaseSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (affineBase B S hS), isAlgebraicSpace_yoneda B S hS _⟩

/-- The algebraic space `X = h_{𝔸¹_S}`. -/
abbrev affineLineAlgebraicSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (affineLineTotal B S hS), isAlgebraicSpace_yoneda B S hS _⟩

/-- The structure morphism `f : X ⟶ Y` of the affine line, as a morphism of algebraic spaces. -/
abbrev affineLineMap : affineLineAlgebraicSpace B S hS ⟶ affineBaseSpace B S hS :=
  ObjectProperty.homMk (yoneda.map (affineLineProj B S hS))

/-- The identity chart of `Y = h_S`, a terminal object of its small étale site. -/
abbrev affineBaseChart : SmallEtale B S hS (affineBaseSpace B S hS).1 :=
  etaleChartOfIso B S hS (Iso.refl (yoneda.obj (affineBase B S hS)))

omit [IsAffine S] in
/-- The identity chart `affineBaseChart` is a terminal object of the small étale site of
`Y = h_S`. -/
theorem isTerminal_affineBaseChart : Nonempty (IsTerminal (affineBaseChart B S hS)) :=
  ⟨isTerminalEtaleChartOfIso B S hS (Iso.refl (yoneda.obj (affineBase B S hS)))⟩

/-- The identity chart `affineBaseChart` of `Y = h_S` is an affine chart. -/
theorem isAffineChart_affineBaseChart :
    IsAffineChart B S hS (affineBaseSpace B S hS).1 (affineBaseChart B S hS) :=
  isAffine_affineBase B S hS

/-- The algebraic space `Y = h_S` is representable by an affine scheme. -/
theorem isAffineSpace_affineBaseSpace : IsAffineSpace B S hS (affineBaseSpace B S hS).1 :=
  ⟨affineBase B S hS, isAffine_affineBase B S hS, ⟨Iso.refl _⟩⟩

/-- The algebraic space `X = h_{𝔸¹_S}` is representable by an affine scheme. -/
theorem isAffineSpace_affineLineAlgebraicSpace :
    IsAffineSpace B S hS (affineLineAlgebraicSpace B S hS).1 :=
  ⟨affineLineTotal B S hS, BigFppfOver.isAffine_affineSpace B S hS 1 _ (isAffine_affineBase B S hS),
    ⟨Iso.refl _⟩⟩

/-- The structure morphism of the affine line is an affine morphism of algebraic spaces. -/
theorem isAffineHom_affineLineMap : IsAffineHom B S hS (affineLineMap B S hS).hom :=
  isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_affineLineAlgebraicSpace B S hS)
    (isAffineSpace_affineBaseSpace B S hS)

omit [IsAffine S] in
/-- The structure morphism `f : X ⟶ Y` of the affine line is representable. -/
theorem relativelyRepresentable_affineLineMap :
    yoneda.relativelyRepresentable (affineLineMap B S hS).hom :=
  Functor.relativelyRepresentable.map yoneda (affineLineProj B S hS)

/-- The morphism of the identity chart `affineBaseChart` to `Y = h_S` is an isomorphism. -/
instance isIso_affineBaseChart_hom : IsIso (affineBaseChart B S hS).1.hom :=
  inferInstanceAs (IsIso (𝟙 (yoneda.obj (affineBase B S hS))))

/-- The fibre product `X ×_Y V₀` over the identity chart `V₀` of `Y` is `𝔸¹_S` itself. -/
def affineLinePullbackIso :
    (relativelyRepresentable_affineLineMap B S hS).pullback (affineBaseChart B S hS).1.hom ≅
      affineLineTotal B S hS :=
  have : IsIso ((relativelyRepresentable_affineLineMap B S hS).fst
      (affineBaseChart B S hS).1.hom) :=
    ((relativelyRepresentable_affineLineMap B S hS).isPullback _).isIso_fst_of_isIso
  Yoneda.fullyFaithful.preimageIso (asIso ((relativelyRepresentable_affineLineMap B S hS).fst
    (affineBaseChart B S hS).1.hom))

omit [IsAffine S] in
/-- Under that identification the projection `X ×_Y V₀ ⟶ V₀` is the structure morphism. -/
theorem affineLinePullbackIso_hom_comp_proj :
    (affineLinePullbackIso B S hS).hom ≫ affineLineProj B S hS =
      (relativelyRepresentable_affineLineMap B S hS).snd (affineBaseChart B S hS).1.hom := by
  apply yoneda.map_injective
  have hj : yoneda.map (affineLinePullbackIso B S hS).hom =
      (relativelyRepresentable_affineLineMap B S hS).fst (affineBaseChart B S hS).1.hom :=
    Yoneda.fullyFaithful.map_preimage _
  rw [Functor.map_comp, hj]
  exact ((relativelyRepresentable_affineLineMap B S hS).isPullback
    (affineBaseChart B S hS).1.hom).w.trans (Category.comp_id _)

/-- The regular functions on `X ×_Y V₀` are those of `𝔸¹_S`. -/
def affineLineChartRingEquiv :
    Γ((BigFppfOver.toScheme B S hS).obj
        ((relativelyRepresentable_affineLineMap B S hS).pullback (affineBaseChart B S hS).1.hom),
        ⊤) ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj (affineLineTotal B S hS), ⊤) :=
  have : IsIso ((BigFppfOver.toScheme B S hS).map (affineLinePullbackIso B S hS).hom).appTop :=
    inferInstanceAs (IsIso (((BigFppfOver.toScheme B S hS).map
      (affineLinePullbackIso B S hS).hom).app ⊤))
  (asIso ((BigFppfOver.toScheme B S hS).map
    (affineLinePullbackIso B S hS).hom).appTop).symm.commRingCatIsoToRingEquiv

omit [IsAffine S] in
/-- The isomorphism `affineLineChartRingEquiv` sends the pullback of `r ∈ Γ(S, 𝒪)` along the
projection `X ×_Y V₀ ⟶ V₀` to its pullback along the structure morphism `𝔸¹_S ⟶ S`. -/
theorem affineLineChartRingEquiv_apply_snd (r : Γ(S, ⊤)) :
    affineLineChartRingEquiv B S hS (((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_affineLineMap B S hS).snd
          (affineBaseChart B S hS).1.hom)).appTop r) =
      (𝔸(ULift.{u} (Fin 1); S) ↘ S).appTop r := by
  have h : ((BigFppfOver.toScheme B S hS).map ((relativelyRepresentable_affineLineMap B S hS).snd
        (affineBaseChart B S hS).1.hom)).appTop r =
      ((BigFppfOver.toScheme B S hS).map (affineLinePullbackIso B S hS).hom).appTop
        (((BigFppfOver.toScheme B S hS).map (affineLineProj B S hS)).appTop r) := by
    have := congrArg (fun φ : (relativelyRepresentable_affineLineMap B S hS).pullback
        (affineBaseChart B S hS).1.hom ⟶ affineBase B S hS =>
          ((BigFppfOver.toScheme B S hS).map φ).appTop r)
      (affineLinePullbackIso_hom_comp_proj B S hS)
    simp only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at this
    exact this.symm
  rw [h]
  have : IsIso ((BigFppfOver.toScheme B S hS).map (affineLinePullbackIso B S hS).hom).appTop :=
    inferInstanceAs (IsIso (((BigFppfOver.toScheme B S hS).map
      (affineLinePullbackIso B S hS).hom).app ⊤))
  change (inv ((BigFppfOver.toScheme B S hS).map (affineLinePullbackIso B S hS).hom).appTop)
    ((((BigFppfOver.toScheme B S hS).map (affineLinePullbackIso B S hS).hom).appTop)
      (((BigFppfOver.toScheme B S hS).map (affineLineProj B S hS)).appTop r)) = _
  rw [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply]
  rfl

/-- The sections of `f_*𝒪_X` over the identity chart of `Y` are the regular functions on
`𝔸¹_S`. -/
def affineLineDirectImageSectionsRingEquiv :
    (pushforwardAlgebra B S hS (Over.mk (affineLineMap B S hS))).right.obj.obj
        (op (affineBaseChart B S hS)) ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj (affineLineTotal B S hS), ⊤) :=
  (pushforwardAlgebraSectionsIso B S hS (Over.mk (affineLineMap B S hS))
      (relativelyRepresentable_affineLineMap B S hS)
      (affineBaseChart B S hS)).commRingCatIsoToRingEquiv.trans
    (affineLineChartRingEquiv B S hS)

omit [IsAffine S] in
/-- That identification carries the structure map of `f_*𝒪_X` to the structure morphism of
`𝔸¹_S` (Stacks 03G8, part (2)). -/
theorem affineLineDirectImageSectionsRingEquiv_algebraMap (r : Γ(S, ⊤)) :
    affineLineDirectImageSectionsRingEquiv B S hS
        ((pushforwardAlgebra B S hS (Over.mk (affineLineMap B S hS))).algebraMap
          (op (affineBaseChart B S hS)) r) =
      (𝔸(ULift.{u} (Fin 1); S) ↘ S).appTop r := by
  have h := congrArg (fun φ => φ r) (fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS
    (Over.mk (affineLineMap B S hS)) (relativelyRepresentable_affineLineMap B S hS)
    (affineBaseChart B S hS))
  exact (congrArg (affineLineChartRingEquiv B S hS) h).trans
    (affineLineChartRingEquiv_apply_snd B S hS r)

/-- **The sections of `f_*𝒪_X` over the identity chart of `Y` are free over `Γ(S, 𝒪)`**, on
the monomials. -/
def affineLineDirectImageSectionsBasis :
    Module.Basis (ULift.{u} (Fin 1) →₀ ℕ)
      (chartRing B S hS (affineBaseSpace B S hS).1 (affineBaseSpace B S hS).2
        (affineBaseChart B S hS))
      ((pushforwardAlgebra B S hS (Over.mk (affineLineMap B S hS))).underlyingModule.val.obj
        (op (affineBaseChart B S hS))) :=
  let ψ : chartRing B S hS (affineBaseSpace B S hS).1 (affineBaseSpace B S hS).2
      (affineBaseChart B S hS) →+* Γ(𝔸(ULift.{u} (Fin 1); S), ⊤) :=
    (𝔸(ULift.{u} (Fin 1); S) ↘ S).appTop.hom
  letI := Module.compHom Γ(𝔸(ULift.{u} (Fin 1); S), ⊤) ψ
  let b₀ : Module.Basis (ULift.{u} (Fin 1) →₀ ℕ)
      (chartRing B S hS (affineBaseSpace B S hS).1 (affineBaseSpace B S hS).2
        (affineBaseChart B S hS)) Γ(𝔸(ULift.{u} (Fin 1); S), ⊤) :=
    affineSpaceGlobalSectionsBasis (ULift.{u} (Fin 1)) S
  b₀.map (linearEquivOfRingEquiv
      ((pushforwardAlgebra B S hS (Over.mk (affineLineMap B S hS))).algebraMap
        (op (affineBaseChart B S hS))) ψ
      (affineLineDirectImageSectionsRingEquiv B S hS)
      (affineLineDirectImageSectionsRingEquiv_algebraMap B S hS)).symm

/-- `ULift (Fin 1) →₀ ℕ`, the monomials in one variable, is `ℕ`. -/
def monomialsOneVariableEquiv : (ULift.{u} (Fin 1) →₀ ℕ) ≃ ULift.{u} ℕ :=
  Finsupp.equivFunOnFinite.trans ((Equiv.funUnique (ULift.{u} (Fin 1)) ℕ).trans Equiv.ulift.symm)

/-- **`f_*𝒪_X ≅ 𝒪_Y^{⊕ ℕ}`** for the affine line `f : X = h_{𝔸¹_S} ⟶ Y = h_S` over an affine
scheme `S`. -/
theorem nonempty_affineLineDirectImageFreeIso :
    Nonempty ((modulePushforward B S hS (affineLineMap B S hS)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (affineLineAlgebraicSpace B S hS))) ≅
      SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (affineBaseSpace B S hS).1 (affineBaseSpace B S hS).2).O)
        (ULift.{u} ℕ)) := by
  obtain ⟨hV₀⟩ := isTerminal_affineBaseChart B S hS
  obtain ⟨e⟩ := nonempty_free_iso_of_basis B S hS (affineBaseSpace B S hS)
    (pushforwardAlgebra B S hS (Over.mk (affineLineMap B S hS))).underlyingModule
    (isQuasicoherent_pushforwardAlgebra_of_isAffineHom B S hS
      (Over.mk (affineLineMap B S hS)) (isAffineHom_affineLineMap B S hS))
    hV₀ (isAffineChart_affineBaseChart B S hS)
    ((affineLineDirectImageSectionsBasis B S hS).reindex monomialsOneVariableEquiv)
  exact ⟨eqToIso (underlyingModule_pushforwardAlgebra B S hS (affineLineMap B S hS)).symm ≪≫
    e.symm⟩

end AffineLine

end AlgebraicGeometry.Space

end
