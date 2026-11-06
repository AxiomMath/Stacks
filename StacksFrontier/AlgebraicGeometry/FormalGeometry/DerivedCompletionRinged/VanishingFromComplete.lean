module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayColimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdeal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionColimit
public import StacksFrontier.CategoryTheory.Abelian.Telescope
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomCoproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomLinearSource
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

attribute [local instance] linearCatCenterRingSheaf

/-- Colimits over `ℕ` of sheaves of `𝒪`-modules are exact. -/
theorem hasExactColimitsOfShape_nat_sheafOfModules :
    HasExactColimitsOfShape ℕ (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  SheafOfModules.DifferentialGradedModule.hasExactColimitsOfShape_nat.{u, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))

attribute [local instance] hasExactColimitsOfShape_nat_sheafOfModules

/-- Multiplication by the global section `f`, as an endomorphism of `𝒪`. -/
abbrev awaySmulUnit :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The sequential diagram `𝒪 --f--> 𝒪 --f--> ⋯`, whose colimit is `𝒪_f`. -/
abbrev awayTelescopeSequence :
    ℕ ⥤ SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  awaySequence X (awaySmulUnit X h)

/-- The telescope map `1 - f·shift : ⊕ₙ 𝒪 ⟶ ⊕ₙ 𝒪`. -/
abbrev awayTelescopeMap :
    (∐ fun n : ℕ => (awayTelescopeSequence X h).obj n) ⟶
      ∐ fun n : ℕ => (awayTelescopeSequence X h).obj n :=
  Sigma.desc fun n : ℕ =>
    Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n -
      (awayTelescopeSequence X h).map (homOfLE n.le_succ) ≫
        Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) (n + 1)

/-- **The telescope presentation of `𝒪_f`**: the short complex
`0 → ⊕ₙ 𝒪 → ⊕ₙ 𝒪 → colim(𝒪 →f 𝒪 → ⋯) → 0` is short exact. -/
theorem awayTelescope_shortExact :
    (ShortComplex.mk (awayTelescopeMap X h)
      (Sigma.desc fun n : ℕ => colimit.ι (awayTelescopeSequence X h) n)
      (Stacks.MappingTelescope.telescope_general_hz _)).ShortExact :=
  Stacks.MappingTelescope.telescope_shortExact_general _
    (Stacks.MappingTelescope.telescope_general_hz _)

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The identification of the colimit of `𝒪 --f--> 𝒪 --f--> ⋯` with `𝒪_f`. -/
def awayColimitIso : colimit (awayTelescopeSequence X h) ≅ awayModule X h :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitAwayModuleCocone X h (awaySmulUnit X h)
      fun U x => awaySmul_app_apply X h _ U x)

/-- `𝒪` placed in degree zero preserves countable direct sums. -/
theorem preservesColimitsOfShape_discrete_singleFunctor (J : Type) [Countable J] :
    PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0) := by
  have h1 : PreservesColimitsOfShape (Discrete J)
      (CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete J)
      (HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0))
  have h2 : PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
    preservesColimitsOfShape_discrete_Q X J
  exact preservesColimitsOfShape_of_natIso
    (DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).symm

/-- **The derived internal Hom out of `⊕ₙ 𝒪` is the product of copies of `K`**, the projections
being induced by the inclusions of the summands followed by `R𝑆heafHom(𝒪, K) = K`. -/
def awayTelescopeIsLimitFan :
    IsLimit (Fan.mk (((derivedSheafHomBifunctor X).flip.obj K).obj
        (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (∐ fun n : ℕ => (awayTelescopeSequence X h).obj n))))
      (fun n : ℕ => ((derivedSheafHomBifunctor X).flip.obj K).map
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
            (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n)).op ≫
        (derivedStructureSheafHomIso X K).hom)) := by
  have hpres := preservesColimitsOfShape_discrete_singleFunctor X ℕ
  have hcofan : IsColimit (Cofan.mk
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (∐ fun n : ℕ => (awayTelescopeSequence X h).obj n))
      (fun n : ℕ => (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
        (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n))) :=
    isColimit_cofan_map (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0)
      (coproductIsCoproduct fun n : ℕ => (awayTelescopeSequence X h).obj n)
  have hprod := preservesLimit_derivedSheafHom_flip X
    (fun n : ℕ => (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
      ((awayTelescopeSequence X h).obj n)) K
  exact isLimitFanCompIso
    (isLimit_fan_map ((derivedSheafHomBifunctor X).flip.obj K) (Cofan.IsColimit.op hcofan))
    fun _ : ℕ => derivedStructureSheafHomIso X K

/-- Multiplication by the global section `f` on `𝒪`, read in `D(𝒪)`, is multiplication by the
central endomorphism `f` of the category of sheaves of `𝒪`-modules. -/
theorem singleFunctor_map_awaySmulUnit :
    (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
        (awaySmulUnit X h) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h) •
        𝟙 (derivedStructureSheaf X) := by
  have hsm : awaySmulUnit X h =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h) •
        𝟙 (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
    (Category.comp_id _).symm
  have h1 : (CochainComplex.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
      (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h) •
        𝟙 (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h) •
        𝟙 ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
    (Functor.linear_iff
        (CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0)).mp inferInstance
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h))
  have h3 : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
      (awaySmulUnit X h) = DerivedCategory.Q.map
        ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
          (awaySmulUnit X h)) := rfl
  rw [h3, hsm, h1, DerivedCategory.Q.map_smul, DerivedCategory.Q.map_id]

/-- The map which multiplication by the global section `f` on `𝒪` induces on derived internal
Hom into `K` is multiplication by `f`. The morphism is taken as a variable so that the statement
can be used at a transition map of the sequential diagram, whose source and target are `𝒪` only
up to definitional unfolding. -/
theorem derivedSheafHom_map_singleFunctor_awaySmul
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ha : a = awaySmulUnit X h) :
    ((derivedSheafHomBifunctor X).flip.obj K).map
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map a).op =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h) •
        𝟙 (((derivedSheafHomBifunctor X).flip.obj K).obj
          (op (derivedStructureSheaf X))) := by
  rw [ha, singleFunctor_map_awaySmulUnit]
  exact derivedSheafHom_map_globalSectionToEnd_source X (awayFamily X h)
    (derivedStructureSheaf X) K

/-- The `n`-th inclusion followed by the telescope map is `ιₙ - f·ιₙ₊₁`. -/
theorem ι_comp_awayTelescopeMap (n : ℕ) :
    Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n ≫ awayTelescopeMap X h =
      Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n -
        (awayTelescopeSequence X h).map (homOfLE n.le_succ) ≫
          Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) (n + 1) :=
  Sigma.ι_desc _ _

/-- The `n`-th inclusion followed by the telescope map, placed in degree zero. -/
theorem singleFunctor_map_ι_comp_awayTelescopeMap (n : ℕ) :
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
        (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n ≫ awayTelescopeMap X h) =
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
          (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n) -
        (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
            ((awayTelescopeSequence X h).map (homOfLE n.le_succ)) ≫
          (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
            (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) (n + 1)) := by
  set S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0
  rw [ι_comp_awayTelescopeMap, S.map_sub, S.map_comp]

/-- The telescope map, read by derived internal Hom into `K` and composed with the `n`-th
projection. -/
theorem derivedSheafHom_awayTelescopeMap_comp_map_ι (n : ℕ) :
    ((derivedSheafHomBifunctor X).flip.obj K).map
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
            (awayTelescopeMap X h)).op ≫
        ((derivedSheafHomBifunctor X).flip.obj K).map
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
            (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n)).op =
      ((derivedSheafHomBifunctor X).flip.obj K).map
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
            (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n)).op -
        ((derivedSheafHomBifunctor X).flip.obj K).map
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
              (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) (n + 1))).op ≫
          ((derivedSheafHomBifunctor X).flip.obj K).map
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
              ((awayTelescopeSequence X h).map (homOfLE n.le_succ))).op := by
  set S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0
  set H := (derivedSheafHomBifunctor X).flip.obj K
  rw [← H.map_comp, ← op_comp, ← S.map_comp, singleFunctor_map_ι_comp_awayTelescopeMap,
    op_sub, H.map_sub, ← H.map_comp, ← op_comp]

/-- **The telescope differential is the Milnor difference map.** The `n`-th projection of the
endomorphism of `∏ₙ K` induced by the telescope map is `πₙ - f·πₙ₊₁`. -/
theorem derivedSheafHom_awayTelescopeMap_comp_proj (n : ℕ) :
    ((derivedSheafHomBifunctor X).flip.obj K).map
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
            (awayTelescopeMap X h)).op ≫
        (((derivedSheafHomBifunctor X).flip.obj K).map
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
              (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n)).op ≫
          (derivedStructureSheafHomIso X K).hom) =
      (((derivedSheafHomBifunctor X).flip.obj K).map
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
            (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n)).op ≫
        (derivedStructureSheafHomIso X K).hom) -
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h) •
        (((derivedSheafHomBifunctor X).flip.obj K).map
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
              (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) (n + 1))).op ≫
          (derivedStructureSheafHomIso X K).hom) := by
  set S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0
  set H := (derivedSheafHomBifunctor X).flip.obj K
  set e := (derivedStructureSheafHomIso X K).hom
  set u := H.map (S.map (awayTelescopeMap X h)).op
  set p := H.map
    (S.map (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n)).op
  set q := H.map
    (S.map (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) (n + 1))).op
  set m := H.map
    (S.map ((awayTelescopeSequence X h).map (homOfLE n.le_succ))).op
  have hop : u ≫ p = p - q ≫ m := derivedSheafHom_awayTelescopeMap_comp_map_ι X h K n
  have hsmul : m =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h) •
        𝟙 (H.obj (op (derivedStructureSheaf X))) :=
    derivedSheafHom_map_singleFunctor_awaySmul X h K _ (awaySequence_map_succ X _ n)
  have hs1 : m ≫ e =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h) • e := by
    rw [hsmul]
    exact (Linear.smul_comp _ _ _ _ _ _).trans (congrArg _ (Category.id_comp e))
  calc u ≫ (p ≫ e) = (u ≫ p) ≫ e := (Category.assoc u p e).symm
    _ = (p - q ≫ m) ≫ e := congrArg (fun φ => φ ≫ e) hop
    _ = p ≫ e - q ≫ (m ≫ e) :=
        (Preadditive.sub_comp _ _ _).trans (congrArg (fun φ => p ≫ e - φ) (Category.assoc q m e))
    _ = p ≫ e -
          Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              (awayFamily X h) • (q ≫ e) :=
        congrArg (fun φ => p ≫ e - φ) ((congrArg (q ≫ ·) hs1).trans (Linear.comp_smul _ _ _ _ _ _))

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Countable products exist in `D(𝒪)`. -/
theorem hasProductsOfShape_nat_derivedCategory :
    HasProductsOfShape ℕ
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules _

attribute [local instance] hasProductsOfShape_nat_derivedCategory

/-- **[Stacks, Tag 0997], the equivalence of conditions (1) and (3).** For a global section `f`
of `𝒪` and `K ∈ D(𝒪)`, the derived internal Hom `R𝑆heafHom_𝒪(𝒪_f, K)` vanishes exactly when
`T(K, f) = 0`, that is exactly when the Milnor difference map `1 - f·shift` is invertible on
`∏ₙ K`.

The proof is the source's: `𝒪_f` is the colimit of `𝒪 --f--> 𝒪 --f--> ⋯`
(`AlgebraicGeometry.RingedSite.isColimitAwayModuleCocone`), so the mapping telescope resolves it
by countable direct sums of copies of `𝒪`
(`Stacks.MappingTelescope.telescope_shortExact_general`); derived internal Hom into `K` turns
that short exact sequence into a distinguished triangle
(`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom`, the contravariant half of
[Stacks, Tag 08JC]) whose second and third vertices are `∏ₙ K` and whose first vertex is
`R𝑆heafHom_𝒪(𝒪_f, K)`; and the map between them is `1 - f·shift`, because derived internal Hom
is `𝒪`-linear in its contravariant variable. The first vertex of a distinguished triangle
vanishes exactly when the opposite map is invertible. -/
@[stacks 0997 "(1) ⇔ (3)"]
theorem memVanishingIdeal_iff_isDerivedCompleteAt :
    MemVanishingIdeal X K h ↔
      IsDerivedCompleteAt K
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (awayFamily X h)) := by
  set S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0
  set H := (derivedSheafHomBifunctor X).flip.obj K
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom X K
    (awayTelescope_shortExact X h).singleTriangle
    (awayTelescope_shortExact X h).singleTriangle_distinguished
  have htri : IsZero (H.obj (op (S.obj (colimit (awayTelescopeSequence X h))))) ↔
      IsIso (H.map (S.map (awayTelescopeMap X h)).op) :=
    Triangle.isZero₁_iff_isIso₂ _ hδ
  -- Identify the first vertex with `R𝑆heafHom(𝒪_f, K)`.
  have hvertex : MemVanishingIdeal X K h ↔
      IsZero (H.obj (op (S.obj (colimit (awayTelescopeSequence X h))))) :=
    (H.mapIso (S.mapIso (awayColimitIso X h)).op).isZero_iff
  -- Identify the second map with the Milnor difference map.
  let e : H.obj (op (S.obj (∐ fun n : ℕ => (awayTelescopeSequence X h).obj n))) ≅
      ∏ᶜ fun _ : ℕ => K :=
    IsLimit.conePointUniqueUpToIso (awayTelescopeIsLimitFan X h K)
      (productIsProduct fun _ : ℕ => K)
  have he : ∀ n : ℕ, e.hom ≫ Pi.π (fun _ : ℕ => K) n =
      H.map (S.map (Sigma.ι (fun n : ℕ => (awayTelescopeSequence X h).obj n) n)).op ≫
        (derivedStructureSheafHomIso X K).hom := fun n =>
    IsLimit.conePointUniqueUpToIso_hom_comp (awayTelescopeIsLimitFan X h K)
      (productIsProduct fun _ : ℕ => K) ⟨n⟩
  have hkey : H.map (S.map (awayTelescopeMap X h)).op ≫ e.hom =
      e.hom ≫ oneSubSmulShift K
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (awayFamily X h)) := by
    refine Pi.hom_ext _ _ fun n => ?_
    rw [Category.assoc, he, Category.assoc, oneSubSmulShift_π, Preadditive.comp_sub,
      Linear.comp_smul, he, he, derivedSheafHom_awayTelescopeMap_comp_proj]
  have hconj : H.map (S.map (awayTelescopeMap X h)).op =
      e.hom ≫ oneSubSmulShift K
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (awayFamily X h)) ≫ e.inv := by
    rw [← Category.assoc, ← hkey, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [hvertex, htri, hconj, isIso_comp_left_iff, isIso_comp_right_iff,
    isDerivedCompleteAt_iff_isIso]

end Derived

end AlgebraicGeometry.RingedSite

end
