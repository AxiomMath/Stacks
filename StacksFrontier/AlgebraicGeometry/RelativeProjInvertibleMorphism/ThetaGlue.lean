module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaUnique

/-!
# The relative `θ` of Stacks Tag 01O9, glued over the charts of `Proj_S(𝒜)`

The local data `…GradedPowerMap.thetaLoc V` of the pushforward form
`𝒪_{Proj_S(𝒜)}(n) ⟶ (r_{ℒ,ψ})_*(ℒ^{⊗ n}|_{U(ψ)})` agree wherever two charts overlap, and so glue
(`…RelativeProjChartGlue.existsUnique_hom_of_chart_nested`). The agreement is checked on the
standard opens `D₊(g)`, `g ∈ 𝒜(V)_+`, of the larger chart: there both data are multiplicative,
both carry `ψ(a)` to `ψ(a)`, every section is `ψ(x)/ψ(g)^j`, and `ψ(g)^j` cancels.

## Main definitions

* `…GradedPowerMap.thetaPush`: **the glued degree-`n` component of `θ` in pushforward form.**

## Main results

* `…GradedPowerMap.thetaLoc_nested`: the nested compatibility of the local data.
* `…GradedPowerMap.restrict_thetaPush`, `…GradedPowerMap.eq_thetaPush`: over the chart of every
  affine open `V` of the base `thetaPush` is the local datum built from [Stacks, Tag 01NK]'s `θ`
  for the induced datum, and it is the only morphism with this property.
* `…GradedPowerMap.thetaPush_mul`: `thetaPush` is multiplicative on every open.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace GradedPowerMap

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- The restriction maps of a direct image of a sheaf of graded algebras are those of the direct
image of its pieces. -/
theorem pushforwardAlgebra_piece_map {X Y : Scheme.{u}} (r : X ⟶ Y)
    (C : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (k : ℤ) {O O' : Y.Opens}
    (i : O' ⟶ O) (z : Γ((Scheme.Modules.pushforward r).obj (C.piece k), O)) :
    ((Stacks.RingedSpace.pushforwardAlgebra r.toLRSHom.toShHom C).piece k).val.map i.op z =
      ((Scheme.Modules.pushforward r).obj (C.piece k)).presheaf.map i.op z := rfl

/-! ### The local datum through `localApp` -/

/-- Read on an open of `Proj_S(𝒜)` through the chart over `V`, the local datum is
multiplicative: it carries a product of sections of degrees `i` and `j` to the product of their
images. -/
theorem localApp_thetaLoc_mul (V : S.Opens) (hV : IsAffineOpen V) (i j : ℤ)
    {W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens} {O : (relativeProj A).scheme.Opens}
    (h : (relativeProj A).chart V hV ''ᵁ W₁ = O) (s : Γ(Otw A i, O)) (t : Γ(Otw A j, O)) :
    localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV (i + j)) h
        (((twD A).algebra.mul i j).app (op O) s t) =
      Stacks.TensorPowerDivision.localMul P.L
        (localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV i) h s)
        (localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV j) h t) := by
  subst h
  exact P.thetaLoc_mul V hV i j W₁ s t

/-- Read on an open of `Proj_S(𝒜)` through the chart over `V`, the local datum carries the
restriction of `ψ(a)` to the restriction of `ψ(a)`, for every `a ∈ 𝒜_d(V)`. -/
theorem localApp_thetaLoc_psiU (V : S.Opens) (hV : IsAffineOpen V) (d : ℕ)
    {W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens} {O : (relativeProj A).scheme.Opens}
    (h : (relativeProj A).chart V hV ''ᵁ W₁ = O) (hO : O ≤ (relativeProj A).toBase ⁻¹ᵁ V)
    (hO' : P.coveringOpen.ι ''ᵁ (P.globalMorphism (relativeProj A) ⁻¹ᵁ O) ≤ f ⁻¹ᵁ V)
    (a : Γ(A.piece (d : ℤ), V)) :
    localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV d) h
        ((Otw A d).presheaf.map (homOfLE hO).op (psiU A d V a)) =
      (tensorPowerModule T P.L d).presheaf.map (homOfLE hO').op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
          (P.value d V a)) := by
  subst h
  exact P.thetaLoc_psiU V hV d W₁ a

/-! ### Naturality in the base open -/

omit P in
/-- `psiU` commutes with restriction along an inclusion `V' ⊆ V` of opens of the base. -/
theorem psiU_res (d : ℕ) {V V' : S.Opens} (hle : V' ≤ V) (a : Γ(A.piece (d : ℤ), V)) :
    psiU A d V' ((A.piece (d : ℤ)).presheaf.map (homOfLE hle).op a) =
      (Otw A d).presheaf.map (homOfLE ((relativeProj A).toBase.preimage_mono hle)).op
        (psiU A d V a) :=
  app_map ((twD A).ψ d) (homOfLE hle).op a

/-- The value of `ψ` in the tensor power `ℒ^{⊗ d}` commutes with restriction along an inclusion
`V' ⊆ V` of opens of the base. -/
theorem powValue_res (d : ℕ) {V V' : S.Opens} (hle : V' ≤ V) (a : Γ(A.piece (d : ℤ), V)) :
    (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V')
        (P.value d V' ((A.piece (d : ℤ)).presheaf.map (homOfLE hle).op a)) =
      (tensorPowerModule T P.L d).presheaf.map (homOfLE (f.preimage_mono hle)).op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
          (P.value d V a)) :=
  (congrArg _ (P.value_res d hle a)).trans (app_map _ _ _)

/-- A degreewise family respects heterogeneous equality across equal degrees. -/
theorem heq_family {F G : ℤ → Type u} (φ : ∀ k, F k → G k) {k k' : ℤ} (h : k = k')
    {a : F k} {b : F k'} (hab : HEq a b) : HEq (φ k a) (φ k' b) := by
  subst h
  rw [eq_of_heq hab]

/-! ### The nested compatibility, on a standard open of the larger chart -/

/-- **On a standard open of the chart over `V`, the local datum over `V' ⊆ V` agrees with the
local datum over `V`.** Both are multiplicative and read `ψ`, every section there is
`ψ(x) / ψ(g)^j`, and multiplication by `ψ(g)^j` is injective. -/
theorem thetaLoc_nested_basicOpen (V : S.Opens) (hV : IsAffineOpen V) (V' : S.Opens)
    (hV' : IsAffineOpen V') (hle : V' ≤ V) {e : ℕ} {g : A.sectionRing V}
    (hg : g ∈ A.grading V e) (he : 0 < e) (n : ℤ) {O : (relativeProj A).scheme.Opens}
    {W₂ : (AlgebraicGeometry.Proj (A.grading V')).Opens}
    (h₁ : (relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g = O)
    (h₂ : (relativeProj A).chart V' hV' ''ᵁ W₂ = O) (t : Γ(Otw A n, O)) :
    localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV n) h₁ t =
      localApp ((relativeProj A).chart V' hV') (P.thetaLoc V' hV' n) h₂ t := by
  subst h₁
  have hO : (relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g ≤
      (relativeProj A).toBase ⁻¹ᵁ V := chart_image_le V hV _
  have hO' : (relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g ≤
      (relativeProj A).toBase ⁻¹ᵁ V' := h₂ ▸ chart_image_le V' hV' W₂
  have hT : P.coveringOpen.ι ''ᵁ (P.globalMorphism (relativeProj A) ⁻¹ᵁ
      ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) ≤
        f ⁻¹ᵁ V' := by
    have := P.targetOpen_le V' hV' W₂
    unfold targetOpen at this
    rwa [h₂] at this
  have hψ : ∀ (d : ℕ) (p : A.grading V d),
      localApp ((relativeProj A).chart V' hV') (P.thetaLoc V' hV' d) h₂
        ((Otw A d).presheaf.map (homOfLE hO).op (psiU A d V (A.componentEquiv V d p))) =
      localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV d) rfl
        ((Otw A d).presheaf.map (homOfLE hO).op (psiU A d V (A.componentEquiv V d p))) := by
    intro d p
    refine Eq.trans ?_ (P.localApp_thetaLoc_psiU V hV d rfl hO
      (P.targetOpen_le V hV _) _).symm
    have e1 : (Otw A d).presheaf.map (homOfLE hO).op (psiU A d V (A.componentEquiv V d p)) =
        (Otw A d).presheaf.map (homOfLE hO').op (psiU A d V' ((A.piece (d : ℤ)).presheaf.map
          (homOfLE hle).op (A.componentEquiv V d p))) := by
      rw [psiU_res]
      exact (map_map _ _ _ _ _).symm
    rw [e1, P.localApp_thetaLoc_psiU V' hV' d h₂ hO' hT, P.powValue_res d hle]
    exact map_map _ _ _ _ _
  obtain ⟨j, N, x, hN, hH⟩ := exists_psiU_mul_eq V hV hg he n t
  have k₁ := heq_family
    (F := fun k => ↑Γ(Otw A k, (relativeProj A).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
    (G := fun k => ↑Γ(tensorPowerModule T P.L k,
      P.targetOpen V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
    (fun k => localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV k) rfl) hN hH
  have k₂ := heq_family
    (F := fun k => ↑Γ(Otw A k, (relativeProj A).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
    (G := fun k => ↑Γ(tensorPowerModule T P.L k,
      P.targetOpen V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
    (fun k => localApp ((relativeProj A).chart V' hV') (P.thetaLoc V' hV' k) h₂) hN hH
  simp only at k₁ k₂
  rw [P.localApp_thetaLoc_mul V hV _ _ rfl] at k₁
  rw [P.localApp_thetaLoc_mul V' hV' _ _ h₂, hψ, hψ] at k₂
  have key := eq_of_heq (k₂.trans k₁.symm)
  rw [P.localApp_thetaLoc_psiU V hV _ rfl hO (P.targetOpen_le V hV _)] at key
  exact (P.psiVal_cancel V hV hg he j n _ _ key).symm

/-- **The nested compatibility of the local data**, over an arbitrary open seen by both charts. -/
theorem thetaLoc_nested (n : ℤ) (m m' : S.affineOpens) (hmm : m'.1 ≤ m.1)
    (O : (relativeProj A).scheme.Opens)
    (W₁ : (AlgebraicGeometry.Proj (A.grading m.1)).Opens)
    (W₂ : (AlgebraicGeometry.Proj (A.grading m'.1)).Opens)
    (h₁ : (relativeProj A).chart m.1 m.2 ''ᵁ W₁ = O)
    (h₂ : (relativeProj A).chart m'.1 m'.2 ''ᵁ W₂ = O) :
    localApp ((relativeProj A).chart m.1 m.2) (P.thetaLoc m.1 m.2 n) h₁ =
      localApp ((relativeProj A).chart m'.1 m'.2) (P.thetaLoc m'.1 m'.2 n) h₂ := by
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  let ι := {p : Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.Idx (A.grading m.1) //
    AlgebraicGeometry.Proj.basicOpen (A.grading m.1) (p.1.2 : A.sectionRing m.1) ≤ W₁}
  let U : ι → (relativeProj A).scheme.Opens := fun k =>
    (relativeProj A).chart m.1 m.2 ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading m.1) (k.1.1.2 : A.sectionRing m.1)
  have hUO : ∀ k, U k ≤ O := fun k => h₁ ▸ Scheme.Hom.image_mono _ k.2
  have hcov : O ≤ ⨆ k, U k := by
    rintro _ hx
    rw [← h₁] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨d, g, hd, hg, hzg, hgW⟩ :=
      Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le (A.grading m.1) hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨⟨d, ⟨g, hg⟩⟩, hd⟩, hgW⟩, ⟨z, hzg, rfl⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (P.pushK n).isSheaf U hUO hcov
    fun k => ?_
  have hk₂ : (relativeProj A).chart m'.1 m'.2 ''ᵁ
      ((relativeProj A).chart m'.1 m'.2 ⁻¹ᵁ U k) = U k :=
    image_preimage_eq_self _ ((hUO k).trans (h₂ ▸ Scheme.Hom.image_mono _ le_top))
  refine (localApp_map _ _ h₁ rfl (hUO k) s).symm.trans ?_
  refine Eq.trans ?_ (localApp_map _ _ h₂ hk₂ (hUO k) s)
  exact P.thetaLoc_nested_basicOpen m.1 m.2 m'.1 m'.2 hmm k.1.1.2.2 k.1.2 n rfl hk₂ _

/-- **The degree-`n` component of the relative `θ`, in pushforward form, exists and is unique**:
there is exactly one morphism `𝒪_{Proj_S(𝒜)}(n) ⟶ (r_{ℒ,ψ})_*(ℒ^{⊗ n}|_{U(ψ)})` restricting on
the chart over each affine open `V` of the base to the local datum built from
[Stacks, Tag 01NK]'s `θ` for the induced datum over `V`. -/
theorem existsUnique_thetaPush (n : ℤ) :
    ∃! φ : Otw A n ⟶ P.pushK n, ∀ m : S.affineOpens,
      (Scheme.Modules.restrictFunctor ((relativeProj A).chart m.1 m.2)).map φ =
        P.thetaLoc m.1 m.2 n :=
  RelativeProjChartGlue.existsUnique_hom_of_chart_nested (relativeProj A)
    (fun m => P.thetaLoc m.1 m.2 n) (P.thetaLoc_nested n)

/-! ### The glued pushforward form -/

/-- **The degree-`n` component of the relative `θ` in pushforward form**,
`𝒪_{Proj_S(𝒜)}(n) ⟶ (r_{ℒ,ψ})_*(ℒ^{⊗ n}|_{U(ψ)})`, glued from the local data over the charts. -/
def thetaPush (n : ℤ) : Otw A n ⟶ P.pushK n :=
  (P.existsUnique_thetaPush n).exists.choose

/-- **Over the chart of an affine open `V` of the base, `θ` is [Stacks, Tag 01NK]'s `θ` for the
induced datum over `V`**, read through the identifications of the local datum. -/
theorem restrict_thetaPush (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ) :
    (Scheme.Modules.restrictFunctor ((relativeProj A).chart V hV)).map (P.thetaPush n) =
      P.thetaLoc V hV n :=
  (P.existsUnique_thetaPush n).exists.choose_spec ⟨V, hV⟩

/-- **`thetaPush` is the only morphism with that restriction property.** -/
theorem eq_thetaPush (n : ℤ) {φ : Otw A n ⟶ P.pushK n}
    (hφ : ∀ (V : S.Opens) (hV : IsAffineOpen V),
      (Scheme.Modules.restrictFunctor ((relativeProj A).chart V hV)).map φ =
        P.thetaLoc V hV n) : φ = P.thetaPush n :=
  (P.existsUnique_thetaPush n).unique (fun m => hφ m.1 m.2)
    (P.existsUnique_thetaPush n).exists.choose_spec

/-- On an open `O` in the image of the chart over an affine open `V` of the base, `thetaPush` is
the local datum over `V`, read through that chart. -/
theorem thetaPush_app_eq_localApp (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ)
    {W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens} {O : (relativeProj A).scheme.Opens}
    (h : (relativeProj A).chart V hV ''ᵁ W₁ = O) (x : Γ(Otw A n, O)) :
    (P.thetaPush n).app O x =
      localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV n) h x :=
  (ConcreteCategory.congr_hom (localApp_restrictFunctor_map ((relativeProj A).chart V hV)
    (P.thetaPush n) h).symm x).trans
    (congrArg (fun φ => localApp ((relativeProj A).chart V hV) φ h x) (P.restrict_thetaPush V hV n))

/-- The image under the chart over an affine open `V` of the preimage of `O ⊓ r⁻¹(V)` is
`O ⊓ r⁻¹(V)`, where `r` is the structure morphism of `Proj_S(𝒜)`. -/
theorem chart_image_preimage (V : S.Opens) (hV : IsAffineOpen V)
    (O : (relativeProj A).scheme.Opens) :
    (relativeProj A).chart V hV ''ᵁ ((relativeProj A).chart V hV ⁻¹ᵁ
      (O ⊓ (relativeProj A).toBase ⁻¹ᵁ V)) = O ⊓ (relativeProj A).toBase ⁻¹ᵁ V :=
  image_preimage_eq_self _ (inf_le_right.trans
    (RelativeProjTwistGlue.chart_image_top (relativeProj A) V hV).ge)

/-- Every open `O` of `Proj_S(𝒜)` is covered by its intersections with the preimages of the
affine opens of the base. -/
theorem iSup_inf_preimage (O : (relativeProj A).scheme.Opens) :
    O ≤ ⨆ m : S.affineOpens, O ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1 := by
  rw [← inf_iSup_eq, ← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top,
    Scheme.Hom.preimage_top, inf_top_eq]

/-- The product of the target of the pushforward form of `θ` is the product of local sections of
the tensor powers. -/
theorem pushforward_laurentOn_mul (i j : ℤ) (O : (relativeProj A).scheme.Opens)
    (a : Γ(P.pushK i, O)) (b : Γ(P.pushK j, O)) :
    ((Stacks.RingedSpace.pushforwardAlgebra
          (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
          (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L
            P.coveringOpen)).mul i j).app
        (op O) a b = Stacks.TensorPowerDivision.localMul P.L a b := rfl

/-- **The relative `θ` is multiplicative**, on every open of `Proj_S(𝒜)`. -/
theorem thetaPush_mul (i j : ℤ) (U : (relativeProj A).scheme.Opensᵒᵖ)
    (x : ((twD A).algebra.piece i).val.obj U) (y : ((twD A).algebra.piece j).val.obj U) :
    (P.thetaPush (i + j)).val.app U (((twD A).algebra.mul i j).app U x y) =
      ((Stacks.RingedSpace.pushforwardAlgebra
          (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
          (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L
            P.coveringOpen)).mul i j).app U
        ((P.thetaPush i).val.app U x) ((P.thetaPush j).val.app U y) := by
  obtain ⟨U⟩ := U
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (P.pushK (i + j)).isSheaf
    (fun m : S.affineOpens => U ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1) (fun _ => inf_le_left)
    (iSup_inf_preimage U) fun m => ?_
  have hle : U ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1 ≤ U := inf_le_left
  refine (Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map (P.thetaPush (i + j)) hle
    (((twD A).algebra.mul i j).app (op U) x y)).trans ?_
  refine Eq.trans (congrArg ((P.thetaPush (i + j)).app (U ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1))
    (((twD A).algebra.mul i j).naturality (homOfLE hle).op x y)) ?_
  refine (P.thetaPush_app_eq_localApp m.1 m.2 (i + j) (chart_image_preimage m.1 m.2 U)
    _).trans ?_
  refine (P.localApp_thetaLoc_mul m.1 m.2 i j (chart_image_preimage m.1 m.2 U) _ _).trans ?_
  have hnatB := ((Stacks.RingedSpace.pushforwardAlgebra
          (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
          (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L
            P.coveringOpen)).mul i j).naturality
    (homOfLE hle).op
      ((P.thetaPush i).val.app (op U) x) ((P.thetaPush j).val.app (op U) y)
  refine Eq.trans ?_ hnatB.symm
  refine Eq.trans ?_ (P.pushforward_laurentOn_mul i j _ _ _).symm
  have hpk : ∀ (k : ℤ) (z : ((twD A).algebra.piece k).val.obj (op U)),
      localApp ((relativeProj A).chart m.1 m.2) (P.thetaLoc m.1 m.2 k)
          (chart_image_preimage m.1 m.2 U) ((Otw A k).presheaf.map (homOfLE hle).op z) =
        ((Stacks.RingedSpace.pushforwardAlgebra
          (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
          (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen)).piece
            k).val.map (homOfLE hle).op ((P.thetaPush k).val.app (op U) z) := fun k z =>
    ((Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map (P.thetaPush k) hle z).trans
      (P.thetaPush_app_eq_localApp m.1 m.2 k (chart_image_preimage m.1 m.2 U) _)).symm.trans
      (pushforwardAlgebra_piece_map (P.globalMorphism (relativeProj A))
        (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen) k
        (homOfLE hle) _).symm
  exact congrArg₂ (Stacks.TensorPowerDivision.localMul P.L) (hpk i x) (hpk j y)

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
