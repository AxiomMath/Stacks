module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalDeRhamComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DifferentialFormsSheaf

/-!
# The de Rham complex of sheaves `𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯` on `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF].  [Stacks, Tag 07J4]
defines, on the small crystalline site, the sheaves of `𝒪_{X/S}`-modules
`Ω^i_{X/S} = ∧^i_{𝒪_{X/S}} Ω_{X/S}` and the de Rham complex

`𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯`

that the universal `S`-derivation `d_{X/S}` gives rise to.  The objects are **sheaves** on
`Cris(X/S)`.

The sheaf `Ω^i_{X/S}` is `...SmallSite.crysFormsSheaf S i` of
`SmallSite/DifferentialFormsSheaf.lean`: the sheaf of `𝒪_{X/S}`-modules associated with the
sectionwise exterior power `U ↦ ∧^i_{𝒪_{X/S}(U)} Ω^{pre}(U)` of the presheaf `Ω^{pre}` of
crystalline differentials, which is how [Stacks, Tag 01CG] computes the exterior power of a sheaf
of modules (the sheaf `Ω_{X/S}` being the sheafification of `Ω^{pre}`, and the sectionwise
exterior power of a presheaf and of its sheafification having the same sheafification).

This file builds the de Rham complex at the level of sheaves.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crysDeRhamNatSheafComplex` — **the de Rham complex `𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯` of
  abelian sheaves on `Cris(X/S)`**, `ℕ`-indexed, read at the coefficient universe `u + 1` in which
  the cohomology of `Cris(X/S)` lives.  It is the termwise sheafification of the de Rham complex
  of abelian presheaves `...SmallSite.crysDeRhamCochainComplex`.
* `crysDeRhamNatSheafComplexXIso` — its degree-`i` term is the abelian sheaf underlying the
  sheaf of `𝒪_{X/S}`-modules `Ω^i_{X/S}` (`crysFormsSheaf`).
* `crysDeRhamNatSheafComplexXZeroIso` — its degree-zero term is `𝒪_{X/S}`.

## Main results

* `toCrysFormsSheafULift_comp_crysDeRhamNatSheafDifferential` — the differential
  `Ω^i_{X/S} ⟶ Ω^{i+1}_{X/S}` of the complex, read through `crysDeRhamNatSheafComplexXIso`,
  extends the de Rham differential of local sections of [Stacks, Tag 07HY] along the canonical
  map from the presheaf of forms to the sheaf; in degree zero that is the universal derivation
  `d_{X/S}`.
* `crysDeRhamNatSheafDifferential_unique` — it is the only morphism of abelian sheaves doing so.
* `crysDeRhamSheafComplex_eq_extend` — the `ℤ`-indexed complex `...SmallSite.crysDeRhamSheafComplex`
  used for [Stacks, Tag 07LM] is this complex extended by zero.

## References

* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07IX](https://stacks.math.columbia.edu/tag/07IX)
* [Stacks Project, Tag 07HY](https://stacks.math.columbia.edu/tag/07HY)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- **The de Rham complex `𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯` of abelian sheaves on the small
crystalline site `Cris(X/S)`**, at the coefficient universe `u + 1`: the termwise sheafification
of the de Rham complex of abelian presheaves `crysDeRhamCochainComplex`, whose differentials are
the de Rham differentials of [Stacks, Tag 07HY] built from the universal `S`-derivation `d_{X/S}`.
Its degree-`i` term is the sheaf `Ω^i_{X/S} = ∧^i_{𝒪_{X/S}} Ω_{X/S}` (`crysFormsSheaf`), by
`crysDeRhamNatSheafComplexXIso`, and its degree-zero term is `𝒪_{X/S}`, by
`crysDeRhamNatSheafComplexXZeroIso`. -/
@[stacks 07J4 "the de Rham complex 𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯ of abelian sheaves on \
Cris(X/S); its terms are the sheaves Ω^i_{X/S} = crysFormsSheaf S i \
(crysDeRhamNatSheafComplexXIso), its degree-zero term is 𝒪_{X/S} \
(crysDeRhamNatSheafComplexXZeroIso), and its differential is the unique map of sheaves \
extending the de Rham differential of local sections \
(toCrysFormsSheafULift_comp_crysDeRhamNatSheafDifferential, \
crysDeRhamNatSheafDifferential_unique)"]
def crysDeRhamNatSheafComplex :
    CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℕ :=
  ((crysAbelianSheafification S).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (crysDeRhamCochainComplex S)

/-- The degree-`i` term of `crysDeRhamNatSheafComplex` is the sheafification of the abelian
presheaf `Ω^i_{X/S}`. -/
theorem crysDeRhamNatSheafComplex_X (i : ℕ) :
    (crysDeRhamNatSheafComplex S).X i =
      (crysAbelianSheafification S).obj (modulePresheaf S (crysDifferentialForms S i)) := rfl

/-- The differential of `crysDeRhamNatSheafComplex` is the sheafification of the de Rham
differential of abelian presheaves. -/
theorem crysDeRhamNatSheafComplex_d (i : ℕ) :
    (crysDeRhamNatSheafComplex S).d i (i + 1) =
      (crysAbelianSheafification S).map (crysDeRhamPresheafHom S i) :=
  congrArg (crysAbelianSheafification S).map (crysDeRhamCochainComplex_d S i)

/-- **The `ℤ`-indexed de Rham complex of abelian sheaves used for [Stacks, Tag 07LM] is
`crysDeRhamNatSheafComplex` extended by zero.** -/
theorem crysDeRhamSheafComplex_eq_extend :
    crysDeRhamSheafComplex S =
      (crysDeRhamNatSheafComplex S).extend ComplexShape.embeddingUpNat := rfl

/-- The canonical morphism from the abelian presheaf `Ω^i_{X/S}`, raised to the universe `u + 1`,
to the abelian sheaf underlying the sheaf of `𝒪_{X/S}`-modules `Ω^i_{X/S}`. -/
abbrev toCrysFormsSheafULift (i : ℕ) :
    modulePresheaf S (crysDifferentialForms S i) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ⟶
      (abelianSheaf (crysFormsSheaf S i)).obj :=
  Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map (toCrysFormsSheaf S i))
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- `toCrysFormsSheafULift` is locally injective. -/
instance isLocallyInjective_toCrysFormsSheafULift (i : ℕ) :
    Presheaf.IsLocallyInjective (smallTopology S) (toCrysFormsSheafULift S i) :=
  haveI := isLocallyInjective_toCrysFormsSheaf S i
  Stacks.Sheaves.UniverseLift.isLocallyInjective_uliftFunctor _

/-- `toCrysFormsSheafULift` is locally surjective. -/
instance isLocallySurjective_toCrysFormsSheafULift (i : ℕ) :
    Presheaf.IsLocallySurjective (smallTopology S) (toCrysFormsSheafULift S i) :=
  haveI := isLocallySurjective_toCrysFormsSheaf S i
  Stacks.Sheaves.UniverseLift.isLocallySurjective_uliftFunctor _

/-- The comparison morphism from the degree-`i` term of `crysDeRhamNatSheafComplex` to the
abelian sheaf underlying `Ω^i_{X/S}`: the transpose of `toCrysFormsSheafULift` across the
sheafification adjunction. -/
def crysDeRhamNatSheafComplexXHom (i : ℕ) :
    (crysDeRhamNatSheafComplex S).X i ⟶ abelianSheaf (crysFormsSheaf S i) :=
  ((sheafificationAdjunction (smallTopology S) AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (toCrysFormsSheafULift S i)

/-- The sheafification map followed by `crysDeRhamNatSheafComplexXHom` is
`toCrysFormsSheafULift`. -/
theorem toSheafify_comp_crysDeRhamNatSheafComplexXHom (i : ℕ) :
    toSheafify (smallTopology S)
        (modulePresheaf S (crysDifferentialForms S i) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) ≫
      (crysDeRhamNatSheafComplexXHom S i).hom = toCrysFormsSheafULift S i := by
  have h := ((sheafificationAdjunction (smallTopology S) AddCommGrpCat.{u + 1}).homEquiv _
    (abelianSheaf (crysFormsSheaf S i))).apply_symm_apply (toCrysFormsSheafULift S i)
  rwa [Adjunction.homEquiv_unit] at h

/-- **A locally bijective morphism from an abelian presheaf on `Cris(X/S)` to a sheaf exhibits the
sheaf as the sheafification**: its transpose across the sheafification adjunction is an
isomorphism. -/
theorem isIso_homEquiv_symm_of_isLocallyBijective
    {P : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    {F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (φ : P ⟶ F.obj)
    [Presheaf.IsLocallyInjective (smallTopology S) φ]
    [Presheaf.IsLocallySurjective (smallTopology S) φ] :
    IsIso (((sheafificationAdjunction (smallTopology S) AddCommGrpCat.{u + 1}).homEquiv P F).symm
      φ) := by
  have := isLocallySurjective_toSheafify P
  have fac : toSheafify (smallTopology S) P ≫
      (((sheafificationAdjunction (smallTopology S) AddCommGrpCat.{u + 1}).homEquiv P F).symm
        φ).hom = φ := by
    have h := ((sheafificationAdjunction (smallTopology S) AddCommGrpCat.{u + 1}).homEquiv P
      F).apply_symm_apply φ
    rwa [Adjunction.homEquiv_unit] at h
  refine (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨?_, ?_⟩
  · exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _ _ fac
  · exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ fac

/-- `crysDeRhamNatSheafComplexXHom` is an isomorphism: `toCrysFormsSheafULift` is locally injective
and locally surjective. -/
instance isIso_crysDeRhamNatSheafComplexXHom (i : ℕ) :
    IsIso (crysDeRhamNatSheafComplexXHom S i) :=
  isIso_homEquiv_symm_of_isLocallyBijective S (toCrysFormsSheafULift S i)

/-- **The degree-`i` term of the de Rham complex of sheaves is `Ω^i_{X/S}`**: the abelian sheaf
underlying the sheaf of `𝒪_{X/S}`-modules `crysFormsSheaf S i`. -/
def crysDeRhamNatSheafComplexXIso (i : ℕ) :
    (crysDeRhamNatSheafComplex S).X i ≅ abelianSheaf (crysFormsSheaf S i) :=
  asIso (crysDeRhamNatSheafComplexXHom S i)

/-- **The degree-zero term of the de Rham complex of sheaves is `𝒪_{X/S}`**: the identification
`Ω^0_{X/S} = 𝒪_{X/S}` of presheaves, sheafified, followed by the sheafification of the structure
sheaf, which is already a sheaf. -/
def crysDeRhamNatSheafComplexXZeroIso :
    (crysDeRhamNatSheafComplex S).X 0 ≅ abelianSheaf (SheafOfModules.unit (structureSheaf S)) :=
  (crysAbelianSheafification S).mapIso
      ((PresheafOfModules.toPresheaf _).mapIso (crysFormsZeroIso S).symm) ≪≫
    (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1}).preimageIso
      (isoSheafify (smallTopology S)
        (abelianSheaf (SheafOfModules.unit (structureSheaf S))).property).symm

/-- **The differential `Ω^i_{X/S} ⟶ Ω^{i+1}_{X/S}` of the de Rham complex of sheaves**, read on
the sheaves `crysFormsSheaf` through `crysDeRhamNatSheafComplexXIso`. -/
def crysDeRhamNatSheafDifferential (i : ℕ) :
    abelianSheaf (crysFormsSheaf S i) ⟶ abelianSheaf (crysFormsSheaf S (i + 1)) :=
  (crysDeRhamNatSheafComplexXIso S i).inv ≫ (crysDeRhamNatSheafComplex S).d i (i + 1) ≫
    (crysDeRhamNatSheafComplexXIso S (i + 1)).hom

/-- `toCrysFormsSheafULift` followed by the inverse of `crysDeRhamNatSheafComplexXIso` is the
sheafification map. -/
theorem toCrysFormsSheafULift_comp_crysDeRhamNatSheafComplexXIso_inv (i : ℕ) :
    toCrysFormsSheafULift S i ≫ (crysDeRhamNatSheafComplexXIso S i).inv.hom =
      toSheafify (smallTopology S)
        (modulePresheaf S (crysDifferentialForms S i) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) := by
  have h : (crysDeRhamNatSheafComplexXHom S i).hom ≫
      (crysDeRhamNatSheafComplexXIso S i).inv.hom = 𝟙 _ :=
    ((sheafToPresheaf _ _).map_comp _ _).symm.trans
      ((congrArg (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1}).map
        (crysDeRhamNatSheafComplexXIso S i).hom_inv_id).trans ((sheafToPresheaf _ _).map_id _))
  exact ((congrArg (· ≫ (crysDeRhamNatSheafComplexXIso S i).inv.hom)
      (toSheafify_comp_crysDeRhamNatSheafComplexXHom S i).symm).trans
    (Category.assoc _ _ _)).trans ((congrArg (_ ≫ ·) h).trans (Category.comp_id _))

/-- **The differential of the de Rham complex of sheaves extends the de Rham differential of local
sections**: composed with the canonical map from the presheaf `Ω^i_{X/S}` to the sheaf, it is the
de Rham differential of [Stacks, Tag 07HY] followed by the canonical map in degree `i + 1`.  In
degree zero this is the universal derivation `d_{X/S}`. -/
theorem toCrysFormsSheafULift_comp_crysDeRhamNatSheafDifferential (i : ℕ) :
    toCrysFormsSheafULift S i ≫ (crysDeRhamNatSheafDifferential S i).hom =
      Functor.whiskerRight (crysDeRhamPresheafHom S i) AddCommGrpCat.uliftFunctor.{u + 1, u} ≫
        toCrysFormsSheafULift S (i + 1) := by
  have h₁ := toCrysFormsSheafULift_comp_crysDeRhamNatSheafComplexXIso_inv S i
  have h₂ := toSheafify_naturality (smallTopology S)
    (Functor.whiskerRight (crysDeRhamPresheafHom S i) AddCommGrpCat.uliftFunctor.{u + 1, u})
  have h₃ := toSheafify_comp_crysDeRhamNatSheafComplexXHom S (i + 1)
  have hd : ((crysDeRhamNatSheafComplex S).d i (i + 1)).hom =
      sheafifyMap (smallTopology S)
        (Functor.whiskerRight (crysDeRhamPresheafHom S i) AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
    congrArg (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1}).map
      (crysDeRhamNatSheafComplex_d S i)
  have hcomp : (crysDeRhamNatSheafDifferential S i).hom =
      (crysDeRhamNatSheafComplexXIso S i).inv.hom ≫
        ((crysDeRhamNatSheafComplex S).d i (i + 1)).hom ≫
          (crysDeRhamNatSheafComplexXHom S (i + 1)).hom :=
    ((sheafToPresheaf _ _).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((sheafToPresheaf _ _).map_comp _ _))
  calc toCrysFormsSheafULift S i ≫ (crysDeRhamNatSheafDifferential S i).hom
      = (toCrysFormsSheafULift S i ≫ (crysDeRhamNatSheafComplexXIso S i).inv.hom) ≫
          ((crysDeRhamNatSheafComplex S).d i (i + 1)).hom ≫
            (crysDeRhamNatSheafComplexXHom S (i + 1)).hom :=
        (congrArg (_ ≫ ·) hcomp).trans (Category.assoc _ _ _).symm
    _ = toSheafify (smallTopology S)
          (modulePresheaf S (crysDifferentialForms S i) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) ≫
          sheafifyMap (smallTopology S) (Functor.whiskerRight (crysDeRhamPresheafHom S i)
            AddCommGrpCat.uliftFunctor.{u + 1, u}) ≫
            (crysDeRhamNatSheafComplexXHom S (i + 1)).hom :=
        congrArg₂ (· ≫ ·) h₁ (congrArg (· ≫ (crysDeRhamNatSheafComplexXHom S (i + 1)).hom) hd)
    _ = (Functor.whiskerRight (crysDeRhamPresheafHom S i) AddCommGrpCat.uliftFunctor.{u + 1, u} ≫
          toSheafify (smallTopology S) (modulePresheaf S (crysDifferentialForms S (i + 1)) ⋙
            AddCommGrpCat.uliftFunctor.{u + 1, u})) ≫
          (crysDeRhamNatSheafComplexXHom S (i + 1)).hom :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h₂.symm)
    _ = _ := (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₃)

/-- **The differential of the de Rham complex of sheaves is the only morphism of abelian sheaves
`Ω^i_{X/S} ⟶ Ω^{i+1}_{X/S}` extending the de Rham differential of local sections.** -/
theorem crysDeRhamNatSheafDifferential_unique (i : ℕ)
    (δ : abelianSheaf (crysFormsSheaf S i) ⟶ abelianSheaf (crysFormsSheaf S (i + 1)))
    (hδ : toCrysFormsSheafULift S i ≫ δ.hom =
      Functor.whiskerRight (crysDeRhamPresheafHom S i) AddCommGrpCat.uliftFunctor.{u + 1, u} ≫
        toCrysFormsSheafULift S (i + 1)) :
    δ = crysDeRhamNatSheafDifferential S i := by
  have h : toSheafify (smallTopology S)
        (modulePresheaf S (crysDifferentialForms S i) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) ≫
        (crysDeRhamNatSheafComplexXHom S i).hom ≫ δ.hom =
      toSheafify (smallTopology S)
        (modulePresheaf S (crysDifferentialForms S i) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) ≫
        (crysDeRhamNatSheafComplexXHom S i).hom ≫ (crysDeRhamNatSheafDifferential S i).hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ δ.hom) (toSheafify_comp_crysDeRhamNatSheafComplexXHom S i)).trans
        (hδ.trans ((toCrysFormsSheafULift_comp_crysDeRhamNatSheafDifferential S i).symm.trans
          ((congrArg (· ≫ (crysDeRhamNatSheafDifferential S i).hom)
            (toSheafify_comp_crysDeRhamNatSheafComplexXHom S i)).symm.trans
              (Category.assoc _ _ _)))))
  have key : (crysDeRhamNatSheafComplexXHom S i).hom ≫ δ.hom =
      (crysDeRhamNatSheafComplexXHom S i).hom ≫ (crysDeRhamNatSheafDifferential S i).hom :=
    sheafify_hom_ext (smallTopology S) _ _ (abelianSheaf (crysFormsSheaf S (i + 1))).property h
  have key' : crysDeRhamNatSheafComplexXHom S i ≫ δ =
      crysDeRhamNatSheafComplexXHom S i ≫ crysDeRhamNatSheafDifferential S i :=
    (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1}).map_injective key
  exact (cancel_epi _).1 key'

/-- **Consecutive differentials of the de Rham complex of sheaves compose to zero.** -/
theorem crysDeRhamNatSheafDifferential_comp (i : ℕ) :
    crysDeRhamNatSheafDifferential S i ≫ crysDeRhamNatSheafDifferential S (i + 1) = 0 := by
  simp only [crysDeRhamNatSheafDifferential, Category.assoc, Iso.hom_inv_id_assoc,
    HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]

end Crystalline.GlobalCrystallineSituation.SmallSite

end
