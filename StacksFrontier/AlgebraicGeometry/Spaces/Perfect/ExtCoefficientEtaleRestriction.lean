module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FlatProperSupportRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexEtaleRestriction
public import StacksFrontier.Algebra.Homology.DerivedCategory.ShiftedHomMapComplexCoefficientIso

/-!
# `Ext` into a supported coefficient complex, on the quasi-compact neighbourhood

Let `(U ⊆ X, j : X' ⟶ X)` be an elementary distinguished square, `f : X ⟶ Y` a morphism and
`𝒢^•` a complex of `𝒪_X`-modules.  For a complex `N` of `𝒪_Y`-modules such that `𝒢^• ⊗ f^*N` is
supported on the closed complement of `U`, restriction along `j` is an isomorphism

`Ext^i_X(E, 𝒢^• ⊗ f^*N) ≅ Ext^i_{X'}(E|_{X'}, 𝒢^•|_{X'} ⊗ (j ≫ f)^*N)`

(Stacks 08GG through the Mayer–Vietoris sequence, and the restriction of the coefficient
complexes, `AlgebraicGeometry.Space.tensorPullbackComplexPullbackIso`).  It is natural in `N` and
compatible with the boundary maps of short exact sequences of coefficient complexes.  This is the
first reduction of the proof of Stacks 08JR: replace `X` by a quasi-compact neighbourhood of the
support of `𝒢^•`.

## Main definitions

* `AlgebraicGeometry.Space.edsRestrictTensorPullbackComplexIso`.
* `AlgebraicGeometry.Space.edsRestrictCoefficientExt`.

## Main results

* `AlgebraicGeometry.Space.bijective_edsRestrictCoefficientExtHom`,
  `AlgebraicGeometry.Space.edsRestrictCoefficientExtHom_naturality` and
  `AlgebraicGeometry.Space.edsRestrictCoefficientExtHom_comp_triangleOfSESδ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor X.1} {fV : V ⟶ X.1}
  (hsq : IsElementaryDistinguishedSquare B S hS X.2 Uo fV)

/-- **The restriction of `𝒢^• ⊗ f^*N` to the étale member of the square** is
`𝒢^•|_{X'} ⊗ (j ≫ f)^*N`, as complexes, naturally in `N`. -/
def edsRestrictTensorPullbackComplexIso (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    tensorPullbackComplex f G ⋙ (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) := by
  haveI := Functor.preservesZeroMorphisms_of_iso (etaleModulePullbackIsoPullbackModules B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
  exact Functor.isoWhiskerLeft (tensorPullbackComplex f G)
      (NatIso.mapHomologicalComplex (etaleModulePullbackIsoPullbackModules B S hS
        (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)) (ComplexShape.up ℤ)) ≪≫
    tensorPullbackComplexPullbackIso (edsEtaleHom B S hS hsq) f G

/-- The coefficient complex `𝒢^• ⊗ f^*N` as an object of `D(𝒪_X)`. -/
abbrev tensorPullbackComplexDerived (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
  DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj N)

/-- The map `Ext^i_X(E, 𝒢^• ⊗ f^*N) ⟶ Ext^i_{X'}(E|_{X'}, 𝒢^•|_{X'} ⊗ (j ≫ f)^*N)`: restriction
along `j` followed by the restriction of the coefficient complex. -/
def edsRestrictCoefficientExtHom (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) (i : ℤ) :
    (E ⟶ (tensorPullbackComplexDerived f G N)⟦i⟧) →+
      ((edsEtaleRestrict B S hS hsq).obj E ⟶ (tensorPullbackComplexDerived
        (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
          N)⟦i⟧) :=
  (Preadditive.rightComp _ ((DerivedCategory.Q.map
      ((edsRestrictTensorPullbackComplexIso hsq f G).hom.app N))⟦i⟧')).comp
    (DerivedCategory.shiftedHomMapComplex (etaleModulePullback.{u, u} B S hS
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)) E
      ((tensorPullbackComplex f G).obj N) i)

/-- `AlgebraicGeometry.Space.edsRestrictCoefficientExtHom` sends `e` to its restriction along `j`,
followed by the shift of the identification of the restricted coefficient complex. -/
theorem edsRestrictCoefficientExtHom_apply (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) (i : ℤ)
    (e : E ⟶ (tensorPullbackComplexDerived f G N)⟦i⟧) :
    edsRestrictCoefficientExtHom hsq f G E N i e =
      ((edsEtaleRestrict B S hS hsq).map e ≫
        ((edsEtaleRestrict B S hS hsq).commShiftIso i).hom.app
          (tensorPullbackComplexDerived f G N)) ≫
        ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategoryFactors.hom.app
            ((tensorPullbackComplex f G).obj N) ≫
          DerivedCategory.Q.map ((edsRestrictTensorPullbackComplexIso hsq f G).hom.app N))⟦i⟧' := by
  refine (congrArg (· ≫ (DerivedCategory.Q.map
      ((edsRestrictTensorPullbackComplexIso hsq f G).hom.app N))⟦i⟧')
    (DerivedCategory.shiftedHomMapComplex_apply (etaleModulePullback.{u, u} B S hS
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)) E
      ((tensorPullbackComplex f G).obj N) i e)).trans ?_
  simp only [Functor.map_comp, Category.assoc]

/-- **The restriction map on `Ext` is natural in the coefficient complex.** -/
theorem edsRestrictCoefficientExtHom_naturality (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    {N N' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (q : N ⟶ N') (i : ℤ) (e : E ⟶ (tensorPullbackComplexDerived f G N)⟦i⟧) :
    edsRestrictCoefficientExtHom hsq f G E N' i
        (e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex f G).map q))⟦i⟧') =
      edsRestrictCoefficientExtHom hsq f G E N i e ≫
        (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).map q))⟦i⟧' := by
  have hψ := DerivedCategory.shiftedHomMapComplex_naturality (etaleModulePullback.{u, u} B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)) E
    ((tensorPullbackComplex f G).map q) i e
  have hκ := congrArg (fun t => (DerivedCategory.Q.map t)⟦i⟧')
    ((edsRestrictTensorPullbackComplexIso hsq f G).hom.naturality q)
  simp only [Functor.map_comp] at hκ
  let Fj := etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)
  change DerivedCategory.shiftedHomMapComplex Fj E _ i _ ≫ _ =
    (DerivedCategory.shiftedHomMapComplex Fj E _ i e ≫ _) ≫ _
  rw [hψ, Category.assoc, Category.assoc]
  exact congrArg (DerivedCategory.shiftedHomMapComplex Fj E _ i e ≫ ·) hκ

/-- **The restriction map on `Ext` is compatible with the boundary maps** of a short exact
sequence of coefficient complexes. -/
theorem edsRestrictCoefficientExtHom_comp_triangleOfSESδ (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (T : ShortComplex (CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) ℤ))
    (hT : ((tensorPullbackComplex f G).mapShortComplex.obj T).ShortExact)
    (hT' : ((tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).mapShortComplex.obj
        T).ShortExact)
    (i : ℤ) (e : ShiftedHom E (tensorPullbackComplexDerived f G T.X₃) i) :
    edsRestrictCoefficientExtHom hsq f G E T.X₁ (i + 1)
        (e.comp (DerivedCategory.triangleOfSESδ hT) (add_comm 1 i)) =
      (show ShiftedHom _ (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) T.X₃) i from
        edsRestrictCoefficientExtHom hsq f G E T.X₃ i e).comp
        (DerivedCategory.triangleOfSESδ hT') (add_comm 1 i) :=
  DerivedCategory.shiftedHomMapComplex_comp_iso_comp_triangleOfSESδ
    (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
    (tensorPullbackComplex f G) (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
    (hC := tensorPullbackComplex_preservesZeroMorphisms f G)
    (hC' := tensorPullbackComplex_preservesZeroMorphisms _ _)
    (edsRestrictTensorPullbackComplexIso hsq f G) E T hT hT' i e

/-- **Restriction to the neighbourhood is bijective on `Ext` into a supported coefficient
complex.** -/
theorem bijective_edsRestrictCoefficientExtHom (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hN : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N)) (i : ℤ) :
    Function.Bijective (edsRestrictCoefficientExtHom hsq f G E N i) := by
  have hb := bijective_edsEtaleRestrict_shiftedHom_of_cohomologySupportedOn B S hS hsq E _ hN i
  let hc := (Iso.homToEquiv (Z := (edsEtaleRestrict B S hS hsq).obj E) ((shiftFunctor _ i).mapIso
    (((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategoryFactors.app
        ((tensorPullbackComplex f G).obj N)) ≪≫
      DerivedCategory.Q.mapIso ((edsRestrictTensorPullbackComplexIso hsq f G).app N))))
  have : (edsRestrictCoefficientExtHom hsq f G E N i : _ → _) = hc ∘ (fun e =>
      (edsEtaleRestrict B S hS hsq).map e ≫
        ((edsEtaleRestrict B S hS hsq).commShiftIso i).hom.app
          (tensorPullbackComplexDerived f G N)) := by
    funext e
    rw [edsRestrictCoefficientExtHom_apply]
    rfl
  rw [this]
  exact hc.bijective.comp hb

/-- **`Ext^i_X(E, 𝒢^• ⊗ f^*N) ≅ Ext^i_{X'}(E|_{X'}, 𝒢^•|_{X'} ⊗ (j ≫ f)^*N)`** for `𝒢^• ⊗ f^*N`
supported on the closed complement of the open member of the square. -/
def edsRestrictCoefficientExt (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hN : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N)) (i : ℤ) :
    (E ⟶ (tensorPullbackComplexDerived f G N)⟦i⟧) ≃+
      ((edsEtaleRestrict B S hS hsq).obj E ⟶ (tensorPullbackComplexDerived
        (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
          N)⟦i⟧) :=
  AddEquiv.ofBijective _ (bijective_edsRestrictCoefficientExtHom hsq f G E N hN i)

/-- The inverse of a bijection intertwining `h` and `g` intertwines `g` and `h`. -/
theorem _root_.AddEquiv.symm_apply_eq_of_apply_eq {α β α' β' : Type*} [Add α] [Add β] [Add α']
    [Add β'] (φ : α ≃+ β) (φ' : α' ≃+ β') (h : α → α') (g : β → β')
    (hφ : ∀ x, φ' (h x) = g (φ x)) (y : β) : φ'.symm (g y) = h (φ.symm y) := by
  apply φ'.injective
  rw [AddEquiv.apply_symm_apply, hφ, AddEquiv.apply_symm_apply]

/-- **The inverse of the restriction is natural in the coefficient complex.** -/
theorem edsRestrictCoefficientExt_symm_naturality (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    {N N' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (hN : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N))
    (hN' : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N'))
    (q : N ⟶ N') (i : ℤ)
    (e : (edsEtaleRestrict B S hS hsq).obj E ⟶ (tensorPullbackComplexDerived
        (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
          N)⟦i⟧) :
    (edsRestrictCoefficientExt hsq f G E N' hN' i).symm
        (e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).map q))⟦i⟧') =
      (edsRestrictCoefficientExt hsq f G E N hN i).symm e ≫
        (DerivedCategory.Q.map ((tensorPullbackComplex f G).map q))⟦i⟧' :=
  AddEquiv.symm_apply_eq_of_apply_eq (edsRestrictCoefficientExt hsq f G E N hN i)
    (edsRestrictCoefficientExt hsq f G E N' hN' i) _ _
    (fun x => edsRestrictCoefficientExtHom_naturality hsq f G E q i x) e

/-- **The inverse of the restriction is compatible with the boundary maps.** -/
theorem edsRestrictCoefficientExt_symm_comp_triangleOfSESδ (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (T : ShortComplex (CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) ℤ))
    (hT : ((tensorPullbackComplex f G).mapShortComplex.obj T).ShortExact)
    (hT' : ((tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).mapShortComplex.obj
        T).ShortExact)
    (hN₁ : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G T.X₁))
    (hN₃ : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G T.X₃))
    (i : ℤ) (e : ShiftedHom ((edsEtaleRestrict B S hS hsq).obj E) (tensorPullbackComplexDerived
      (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
        T.X₃) i) :
    (edsRestrictCoefficientExt hsq f G E T.X₁ hN₁ (i + 1)).symm
        (e.comp (DerivedCategory.triangleOfSESδ hT') (add_comm 1 i)) =
      (show ShiftedHom E (tensorPullbackComplexDerived f G T.X₃) i from
        (edsRestrictCoefficientExt hsq f G E T.X₃ hN₃ i).symm e).comp
          (DerivedCategory.triangleOfSESδ hT) (add_comm 1 i) :=
  AddEquiv.symm_apply_eq_of_apply_eq (edsRestrictCoefficientExt hsq f G E T.X₃ hN₃ i)
    (edsRestrictCoefficientExt hsq f G E T.X₁ hN₁ (i + 1))
    (fun x => (show ShiftedHom E (tensorPullbackComplexDerived f G T.X₃) i from x).comp
      (DerivedCategory.triangleOfSESδ hT) (add_comm 1 i))
    (fun y => (show ShiftedHom _ (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) T.X₃) i from y).comp
        (DerivedCategory.triangleOfSESδ hT') (add_comm 1 i))
    (fun x => edsRestrictCoefficientExtHom_comp_triangleOfSESδ hsq f G E T hT hT' i x) e



/-- `AlgebraicGeometry.Space.edsRestrictCoefficientExt` with source and target written as
`ShiftedHom`. -/
def edsRestrictCoefficientShiftedExt (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hN : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N)) (i : ℤ) :
    ShiftedHom E (tensorPullbackComplexDerived f G N) i ≃+
      ShiftedHom ((edsEtaleRestrict B S hS hsq).obj E) (tensorPullbackComplexDerived
        (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
          N) i :=
  edsRestrictCoefficientExt hsq f G E N hN i

/-- `AlgebraicGeometry.Space.edsRestrictCoefficientShiftedExt` sends `e` to its image under
`DerivedCategory.shiftedHomMapComplex`, composed with the shift of the identification of the
restricted coefficient complex. -/
theorem edsRestrictCoefficientShiftedExt_apply (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hN : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N)) (i : ℤ)
    (e : ShiftedHom E (tensorPullbackComplexDerived f G N) i) :
    edsRestrictCoefficientShiftedExt hsq f G E N hN i e =
      DerivedCategory.shiftedHomMapComplex (etaleModulePullback.{u, u} B S hS
          (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)) E
          ((tensorPullbackComplex f G).obj N) i e ≫
        (DerivedCategory.Q.map ((edsRestrictTensorPullbackComplexIso hsq f G).hom.app N))⟦i⟧' :=
  rfl

/-- The inverse of `AlgebraicGeometry.Space.edsRestrictCoefficientShiftedExt` is natural in the
coefficient complex. -/
theorem edsRestrictCoefficientShiftedExt_symm_naturality (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    {N N' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (hN : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N))
    (hN' : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N'))
    (q : N ⟶ N') (i : ℤ)
    (e : ShiftedHom ((edsEtaleRestrict B S hS hsq).obj E) (tensorPullbackComplexDerived
        (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
          N) i) :
    (edsRestrictCoefficientShiftedExt hsq f G E N' hN' i).symm
        (e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).map q))⟦i⟧') =
      (edsRestrictCoefficientShiftedExt hsq f G E N hN i).symm e ≫
        (DerivedCategory.Q.map ((tensorPullbackComplex f G).map q))⟦i⟧' :=
  edsRestrictCoefficientExt_symm_naturality hsq f G E hN hN' q i e

/-- The inverse of `AlgebraicGeometry.Space.edsRestrictCoefficientShiftedExt` is compatible with
the boundary maps of a short exact sequence of coefficient complexes. -/
theorem edsRestrictCoefficientShiftedExt_symm_comp_triangleOfSESδ (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (T : ShortComplex (CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) ℤ))
    (hT : (T.map (tensorPullbackComplex f G)).ShortExact)
    (hT' : (T.map (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).ShortExact)
    (hN₁ : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G T.X₁))
    (hN₃ : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G T.X₃))
    (i : ℤ) (e : ShiftedHom ((edsEtaleRestrict B S hS hsq).obj E) (tensorPullbackComplexDerived
      (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
        T.X₃) i) :
    (edsRestrictCoefficientShiftedExt hsq f G E T.X₁ hN₁ (i + 1)).symm
        (e.comp (DerivedCategory.triangleOfSESδ hT') (add_comm 1 i)) =
      ((edsRestrictCoefficientShiftedExt hsq f G E T.X₃ hN₃ i).symm e).comp
          (DerivedCategory.triangleOfSESδ hT) (add_comm 1 i) :=
  edsRestrictCoefficientExt_symm_comp_triangleOfSESδ hsq f G E T hT hT' hN₁ hN₃ i e


/-- `AlgebraicGeometry.Space.edsRestrictCoefficientShiftedExt_symm_comp_triangleOfSESδ` for the
short complex `N₁ ⟶ N₂ ⟶ N₃` given by its terms and maps. -/
theorem edsRestrictCoefficientShiftedExt_symm_comp_triangleOfSESδ_mk (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    {N₁ N₂ N₃ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (a : N₁ ⟶ N₂) (b : N₂ ⟶ N₃) (hab : a ≫ b = 0)
    (hT : ((ShortComplex.mk a b hab).map (tensorPullbackComplex f G)).ShortExact)
    (hT' : ((ShortComplex.mk a b hab).map (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).ShortExact)
    (hN₁ : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N₁))
    (hN₃ : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N₃))
    (i : ℤ) (e : ShiftedHom ((edsEtaleRestrict B S hS hsq).obj E) (tensorPullbackComplexDerived
      (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
        N₃) i) :
    (edsRestrictCoefficientShiftedExt hsq f G E N₁ hN₁ (i + 1)).symm
        (e.comp (DerivedCategory.triangleOfSESδ hT') (add_comm 1 i)) =
      ((edsRestrictCoefficientShiftedExt hsq f G E N₃ hN₃ i).symm e).comp
          (DerivedCategory.triangleOfSESδ hT) (add_comm 1 i) := by
  simpa only using edsRestrictCoefficientShiftedExt_symm_comp_triangleOfSESδ hsq f G E
    (ShortComplex.mk a b hab) hT hT' hN₁ hN₃ i e

/-- **The restriction to `V` on `Ext` is natural in the coefficient complex**, on `ShiftedHom`. -/
theorem edsRestrictCoefficientShiftedExt_naturality (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    {N N' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (hN : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N))
    (hN' : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N'))
    (q : N ⟶ N') (i : ℤ) (e : ShiftedHom E (tensorPullbackComplexDerived f G N) i) :
    edsRestrictCoefficientShiftedExt hsq f G E N' hN' i
        (e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex f G).map q))⟦i⟧') =
      edsRestrictCoefficientShiftedExt hsq f G E N hN i e ≫
        (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).map q))⟦i⟧' :=
  edsRestrictCoefficientExtHom_naturality hsq f G E q i e

/-- `AlgebraicGeometry.Space.edsRestrictCoefficientShiftedExt` agrees with
`AlgebraicGeometry.Space.edsRestrictCoefficientExtHom`. -/
theorem edsRestrictCoefficientShiftedExt_eq_hom (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hN : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo)
      (tensorPullbackComplexDerived f G N)) (i : ℤ)
    (e : ShiftedHom E (tensorPullbackComplexDerived f G N) i) :
    edsRestrictCoefficientShiftedExt hsq f G E N hN i e =
      edsRestrictCoefficientExtHom hsq f G E N i e :=
  rfl

/-- `AlgebraicGeometry.Space.edsRestrictCoefficientExtHom_comp_triangleOfSESδ` with the short
complexes written through `ShortComplex.map`. -/
theorem edsRestrictCoefficientExtHom_comp_triangleOfSESδ_map (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (T : ShortComplex (CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) ℤ))
    (hT : (T.map (tensorPullbackComplex f G)).ShortExact)
    (hT' : (T.map (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).ShortExact)
    (i : ℤ) (e : ShiftedHom E (tensorPullbackComplexDerived f G T.X₃) i) :
    edsRestrictCoefficientExtHom hsq f G E T.X₁ (i + 1)
        (e.comp (DerivedCategory.triangleOfSESδ hT) (add_comm 1 i)) =
      ShiftedHom.comp (Y := tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) T.X₃)
        (edsRestrictCoefficientExtHom hsq f G E T.X₃ i e)
        (DerivedCategory.triangleOfSESδ hT') (add_comm 1 i) :=
  edsRestrictCoefficientExtHom_comp_triangleOfSESδ hsq f G E T hT hT' i e

/-- **The restriction to `V` on `Ext` is compatible with the boundary maps** of a short exact
sequence `N₁ ⟶ N₂ ⟶ N₃` of coefficient complexes given by its terms and maps. -/
theorem edsRestrictCoefficientExtHom_comp_triangleOfSESδ_mk (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    {N₁ N₂ N₃ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (a : N₁ ⟶ N₂) (b : N₂ ⟶ N₃) (hab : a ≫ b = 0)
    (hT : ((ShortComplex.mk a b hab).map (tensorPullbackComplex f G)).ShortExact)
    (hT' : ((ShortComplex.mk a b hab).map (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).ShortExact)
    (i : ℤ) (e : ShiftedHom E (tensorPullbackComplexDerived f G N₃) i) :
    edsRestrictCoefficientExtHom hsq f G E N₁ (i + 1)
        (e.comp (DerivedCategory.triangleOfSESδ hT) (add_comm 1 i)) =
      ShiftedHom.comp (Y := tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) N₃)
        (edsRestrictCoefficientExtHom hsq f G E N₃ i e)
        (DerivedCategory.triangleOfSESδ hT') (add_comm 1 i) := by
  simpa only using edsRestrictCoefficientExtHom_comp_triangleOfSESδ_map hsq f G E
    (ShortComplex.mk a b hab) hT hT' i e

end AlgebraicGeometry.Space

end
