module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Sections
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleRestrictChart

/-!
# The Čech multifork of a finite open cover, and integral transforms

Let `X` be a scheme and `U_1, …, U_n` a family of open subschemes with quasi-compact and
quasi-separated inclusions.  For a quasi-coherent `𝒪_X`-module `G` the Čech multifork

`G ⟶ ∏ (U_i)_*(G|_{U_i}) ⇉ ∏ (U_i ∩ U_j)_*(G|_{U_i ∩ U_j})`

is formed in `QCoh(𝒪_X)`.  This file proves that **the integral transform
`F_K = pr_{2,*}(pr_1^*(−) ⊗ K)` of any quasi-coherent kernel `K` on `X ×_R Y` carries it to a
limit** as soon as the `U_i` cover `X`, even though `F_K` is only right exact.  This is the
exactness of the bottom row of the comparison diagram in the proof of [Stacks, Tag 0GPA]: the
row computes `F_K(G)` as the kernel of the first relative Čech differential.

The argument is local on `X ×_R Y`.  A cone of sheaves of modules is a limit as soon as its
restrictions to the members of an open cover are
(`AlgebraicGeometry.isLimitOfIsLimitRestrict`).  Over `pr_1^{-1}(U_k)` the functor
`pr_1^*(−) ⊗ K` only sees the restriction to `U_k`
(`AlgebraicGeometry.pullbackTensorKernelRestrictIso`), and the restriction of the Čech
multifork to a member `U_k` of the family is split
(`AlgebraicGeometry.isLimitMapConeRestrictCechMultifork`), so any functor carries it to a limit.
Direct image along the second projection preserves limits, being a right adjoint.

## Main definitions

* `AlgebraicGeometry.qcohRestrict` and `AlgebraicGeometry.qcohRestrictAdjunction`: restriction
  of quasi-coherent modules along an open immersion, left adjoint to direct image.
* `AlgebraicGeometry.cechObj`, `AlgebraicGeometry.cechUnit` and `AlgebraicGeometry.cechRestr`:
  the functor `G ↦ (V ↪ X)_*(G|_V)`, its unit and its restriction maps.
* `AlgebraicGeometry.cechMultifork`: **the Čech multifork** of a family of opens.

## Main results

* `AlgebraicGeometry.isLimitOfSplitMulticospan`: a cone over a multicospan of shape
  `ι ⊔ ι × ι` split at one index is a limit.
* `AlgebraicGeometry.restrictPushModMap_app`: the restriction maps on sections.
* `AlgebraicGeometry.isLimitIntegralTransformCechMultifork`: **the integral transform of a kernel
  carries the Čech multifork of a finite open cover to a limit.**

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Split cones over a multicospan -/

section Split

variable {C : Type*} [Category C] {ι : Type*}
  {D : WalkingMulticospan (MulticospanShape.prod ι) ⥤ C}

/-- The first leg `i ⟶ (i, j)` of the multicospan of shape `prod ι`. -/
abbrev multicospanFst (b : ι × ι) :
    (WalkingMulticospan.left b.1 : WalkingMulticospan (MulticospanShape.prod ι)) ⟶
      WalkingMulticospan.right b :=
  WalkingMulticospan.Hom.fst (J := MulticospanShape.prod ι) b

/-- The second leg `j ⟶ (i, j)` of the multicospan of shape `prod ι`. -/
abbrev multicospanSnd (b : ι × ι) :
    (WalkingMulticospan.left b.2 : WalkingMulticospan (MulticospanShape.prod ι)) ⟶
      WalkingMulticospan.right b :=
  WalkingMulticospan.Hom.snd (J := MulticospanShape.prod ι) b

/-- **A cone over a multicospan split at one index is a limit.** -/
def isLimitOfSplitMulticospan (c : Cone D) (k : ι)
    (s : D.obj (.left k) ⟶ c.pt) (t : ∀ i : ι, D.obj (.right (k, i)) ⟶ D.obj (.left i))
    (hs : c.π.app (.left k) ≫ s = 𝟙 c.pt)
    (ht : ∀ i : ι, D.map (multicospanSnd (k, i)) ≫ t i = 𝟙 _)
    (hst : ∀ i : ι, s ≫ c.π.app (.left i) = D.map (multicospanFst (k, i)) ≫ t i) :
    IsLimit c := by
  have hl : ∀ (E : Cone D) (i : ι),
      (E.π.app (.left k) ≫ s) ≫ c.π.app (.left i) = E.π.app (.left i) := by
    intro E i
    have h1 : E.π.app (.left k) ≫ D.map (multicospanFst (k, i)) =
        E.π.app (.right (k, i)) := E.w (multicospanFst (k, i))
    have h2 : E.π.app (.left i) ≫ D.map (multicospanSnd (k, i)) =
        E.π.app (.right (k, i)) := E.w (multicospanSnd (k, i))
    rw [Category.assoc, hst i, ← Category.assoc, h1, ← h2, Category.assoc, ht i,
      Category.comp_id]
  exact
    { lift := fun E => E.π.app (.left k) ≫ s
      fac := by
        rintro E (i | ⟨a, b⟩)
        · exact hl E i
        · have hc : c.π.app (.left a) ≫ D.map (multicospanFst (a, b)) =
              c.π.app (.right (a, b)) := c.w (multicospanFst (a, b))
          have hE : E.π.app (.left a) ≫ D.map (multicospanFst (a, b)) =
              E.π.app (.right (a, b)) := E.w (multicospanFst (a, b))
          rw [← hc, ← Category.assoc, hl E a, hE]
      uniq := by
        intro E m hm
        rw [← hm (.left k), Category.assoc, hs, Category.comp_id] }

/-- **A functor carries a cone split at one index to a limit cone.** -/
def isLimitMapConeOfSplitMulticospan {C' : Type*} [Category C'] (G : C ⥤ C') (c : Cone D)
    (k : ι) (s : D.obj (.left k) ⟶ c.pt) (t : ∀ i : ι, D.obj (.right (k, i)) ⟶ D.obj (.left i))
    (hs : c.π.app (.left k) ≫ s = 𝟙 c.pt)
    (ht : ∀ i : ι, D.map (multicospanSnd (k, i)) ≫ t i = 𝟙 _)
    (hst : ∀ i : ι, s ≫ c.π.app (.left i) = D.map (multicospanFst (k, i)) ≫ t i) :
    IsLimit (G.mapCone c) :=
  isLimitOfSplitMulticospan (G.mapCone c) k (G.map s) (fun i => G.map (t i))
    (by rw [Functor.mapCone_π_app, ← G.map_comp, hs, G.map_id]; rfl)
    (fun i => by rw [Functor.comp_map, ← G.map_comp, ht i, G.map_id]; rfl)
    (fun i => by rw [Functor.mapCone_π_app, Functor.comp_map, ← G.map_comp, hst i, G.map_comp])

end Split

/-! ### Limits of sheaves of modules are local -/

/-- **A cone of sheaves of modules on a scheme is a limit as soon as its restrictions to the
members of an open cover are.** -/
def isLimitOfIsLimitRestrict {S : Scheme.{u}} {J : Type u} [SmallCategory J] {D : J ⥤ S.Modules}
    (c : Cone D) {ι : Type*} (V : ι → S.Opens) (hV : IsOpenCover V)
    (h : ∀ k, IsLimit ((Scheme.Modules.restrictFunctor (V k).ι).mapCone c)) : IsLimit c := by
  let hL := limit.isLimit D
  have : IsIso (hL.lift c) := by
    refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _ V hV fun k => ?_
    have := StacksTag09NE.restrictFunctor_preservesLimits (V k).ι
    let hL' := isLimitOfPreserves (Scheme.Modules.restrictFunctor (V k).ι) hL
    have e : (Scheme.Modules.restrictFunctor (V k).ι).map (hL.lift c) =
        (IsLimit.conePointUniqueUpToIso (h k) hL').hom :=
      hL'.hom_ext fun j => by
        rw [IsLimit.conePointUniqueUpToIso_hom_comp]
        simp only [Functor.mapCone_π_app, ← Functor.map_comp, IsLimit.fac]
    rw [e]
    infer_instance
  exact IsLimit.ofPointIso hL

/-! ### Restriction of quasi-coherent modules along an open immersion -/

section QcohRestrict

variable {Z X : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f]

/-- Restriction of quasi-coherent modules along an open immersion. -/
def qcohRestrict : Scheme.QuasicoherentModules X ⥤ Scheme.QuasicoherentModules Z :=
  (SheafOfModules.isQuasicoherent Z.ringCatSheaf).lift
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ Scheme.Modules.restrictFunctor f)
    fun M => have : M.obj.IsQuasicoherent := M.property
      Scheme.Modules.isQuasicoherent_restrictFunctor f M.obj

variable [QuasiCompact f] [QuasiSeparated f]

/-- **Restriction is left adjoint to direct image on quasi-coherent modules.** -/
def qcohRestrictAdjunction : qcohRestrict f ⊣ quasicoherentPushforward f :=
  (Scheme.Modules.restrictAdjunction f).restrictFullyFaithful
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).fullyFaithfulι
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

/-- The underlying morphism of modules of the unit of `qcohRestrictAdjunction f` at `G` is the
unit of `Scheme.Modules.restrictAdjunction f` at the underlying module of `G`. -/
theorem qcohRestrictAdjunction_unit_app_hom (G : Scheme.QuasicoherentModules X) :
    ((qcohRestrictAdjunction f).unit.app G).hom =
      (Scheme.Modules.restrictAdjunction f).unit.app G.obj := by
  refine (Adjunction.map_restrictFullyFaithful_unit_app (Scheme.Modules.restrictAdjunction f)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).fullyFaithfulι
    (L := qcohRestrict f) (R := quasicoherentPushforward f)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm G).trans ?_
  simp only [ObjectProperty.liftCompιIso, Iso.symm_hom, Iso.refl_inv, NatTrans.id_app]
  rfl

end QcohRestrict

/-! ### Restriction to an open followed by direct image -/

section RestrictPush

variable {X : Scheme.{u}}

/-- Any two restriction maps of a module with the same source and target agree. -/
private alias presheaf_map_eq' := presheaf_map_eq

/-- A restriction map of a module between equal opens is invertible. -/
private lemma isIso_presheaf_map_of_eq (M : X.Modules) {P Q : (X.Opens)ᵒᵖ} (h : P ⟶ Q)
    (e : P = Q) : IsIso (M.presheaf.map h) := by
  subst e
  rw [Subsingleton.elim h (𝟙 _), CategoryTheory.Functor.map_id]
  infer_instance

/-- `M ↦ (V ↪ X)_*(M|_V)` on all modules. -/
abbrev restrictPushMod (V : X.Opens) : X.Modules ⥤ X.Modules :=
  Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pushforward V.ι

/-- **The restriction map `(V ↪ X)_*(M|_V) ⟶ (W ↪ X)_*(M|_W)`** for opens `W ≤ V`:  the direct
image along `V` of the unit of restriction to `W` inside `V`, followed by the identification of
the iterated restriction and direct image with the ones along `W`. -/
def restrictPushModMap {V W : X.Opens} (h : W ≤ V) (M : X.Modules) :
    (restrictPushMod V).obj M ⟶ (restrictPushMod W).obj M :=
  (Scheme.Modules.pushforward V.ι).map ((Scheme.Modules.restrictAdjunction (X.homOfLE h)).unit.app
      (Scheme.Modules.restrict M V.ι)) ≫
    (Scheme.Modules.pushforwardComp (X.homOfLE h) V.ι).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (Scheme.homOfLE_ι X h)).hom.app _ ≫
    (Scheme.Modules.pushforward W.ι).map
      (restrictCompIso (X.homOfLE h) V.ι (Scheme.homOfLE_ι X h) M).inv

private lemma restrictFunctor_map_app' {Z : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f]
    {M N : X.Modules} (φ : M ⟶ N) (O : Z.Opens) :
    ((Scheme.Modules.restrictFunctor f).map φ).app O = φ.app (f ''ᵁ O) := rfl

private lemma hom_app_naturality {M N : X.Modules} (φ : M ⟶ N) {P Q : (X.Opens)ᵒᵖ} (i : P ⟶ Q) :
    M.presheaf.map i ≫ φ.app Q.unop = φ.app P.unop ≫ N.presheaf.map i :=
  φ.mapPresheaf.naturality i

private lemma presheaf_map_chain_apply (M : X.Modules) {P₀ P₁ P₂ P₃ P₄ : (X.Opens)ᵒᵖ}
    (h₁ : P₀ ⟶ P₁) (h₂ : P₁ ⟶ P₂) (h₃ : P₂ ⟶ P₃) (h₄ : P₃ ⟶ P₄) (k : P₀ ⟶ P₄)
    (x : M.presheaf.obj P₀) :
    M.presheaf.map h₄ (M.presheaf.map h₃ (M.presheaf.map h₂ (M.presheaf.map h₁ x))) =
      M.presheaf.map k x := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← M.presheaf.map_comp, ← M.presheaf.map_comp, ← M.presheaf.map_comp,
    presheaf_map_eq' M (h₁ ≫ h₂ ≫ h₃ ≫ h₄) k]

/-- **The restriction map on sections**: over an open `T` it is the restriction of `M` from
`V ∩ T` to `W ∩ T`. -/
theorem restrictPushModMap_app {V W : X.Opens} (h : W ≤ V) (M : X.Modules) (T : X.Opens) :
    (restrictPushModMap h M).app T =
      M.presheaf.map (homOfLE (by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
          Scheme.Hom.image_preimage_eq_opensRange_inf,
          Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
        exact inf_le_inf_right _ h :
          W.ι ''ᵁ W.ι ⁻¹ᵁ T ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ T)).op := by
  ext x
  simp only [restrictPushModMap, restrictCompIso, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictAdjunction_unit_app_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, Scheme.Modules.restrict_map]
  exact presheaf_map_chain_apply (P₀ := op (V.ι ''ᵁ V.ι ⁻¹ᵁ T)) M _ _ _ _ _ x

/-- **The unit of restriction to `V`, followed by the restriction map to `W ≤ V`, is the unit of
restriction to `W`.** -/
@[reassoc]
theorem restrictAdjunction_unit_comp_restrictPushModMap {V W : X.Opens} (h : W ≤ V)
    (M : X.Modules) :
    (Scheme.Modules.restrictAdjunction V.ι).unit.app M ≫ restrictPushModMap h M =
      (Scheme.Modules.restrictAdjunction W.ι).unit.app M := by
  refine Scheme.Modules.hom_ext _ _ fun O => ?_
  rw [Scheme.Modules.Hom.comp_app, restrictPushModMap_app,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  exact (M.presheaf.map_comp _ _).symm.trans (presheaf_map_eq' M _ _)

/-- The restriction maps are natural in the module. -/
@[reassoc]
theorem restrictPushModMap_naturality {V W : X.Opens} (h : W ≤ V) {M N : X.Modules}
    (φ : M ⟶ N) :
    (restrictPushMod V).map φ ≫ restrictPushModMap h N =
      restrictPushModMap h M ≫ (restrictPushMod W).map φ := by
  refine Scheme.Modules.hom_ext _ _ fun O => ?_
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, restrictPushModMap_app,
    restrictPushModMap_app]
  exact (hom_app_naturality φ _).symm

/-- The restriction to `V` of the unit of restriction to `V` is invertible. -/
instance isIso_restrictFunctor_map_unit (V : X.Opens) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.restrictAdjunction V.ι).unit.app M)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.restrictAdjunction V.ι).unit.app M) ≫
        (Scheme.Modules.restrictAdjunction V.ι).counit.app
          ((Scheme.Modules.restrictFunctor V.ι).obj M)) := by
    rw [(Scheme.Modules.restrictAdjunction V.ι).left_triangle_components M]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.restrictAdjunction V.ι).counit.app
    ((Scheme.Modules.restrictFunctor V.ι).obj M))

/-- **The restriction map from `V` to `W` is invertible over an open `Z` on which `V` and `W`
agree.** -/
theorem isIso_restrictFunctor_map_restrictPushModMap {V W Z : X.Opens} (h : W ≤ V)
    (hZ : Z ⊓ V ≤ W) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor Z.ι).map (restrictPushModMap h M)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro O
  rw [restrictFunctor_map_app', restrictPushModMap_app]
  refine isIso_presheaf_map_of_eq M _ ?_
  have hO : Z.ι ''ᵁ O ≤ Z := (Z.ι.image_le_opensRange O).trans (by simp)
  congr 1
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
  exact le_antisymm
    (le_inf ((le_inf (inf_le_right.trans hO) inf_le_left).trans hZ) inf_le_right)
    (inf_le_inf_right _ h)

end RestrictPush

/-! ### The Čech multifork of a finite family of opens, on quasi-coherent modules -/

section CechQcoh

variable {X : Scheme.{u}}

/-- `G ↦ (V ↪ X)_*(G|_V)` on quasi-coherent modules. -/
abbrev cechObj (V : X.Opens) [QuasiCompact V.ι] [QuasiSeparated V.ι] :
    Scheme.QuasicoherentModules X ⥤ Scheme.QuasicoherentModules X :=
  qcohRestrict V.ι ⋙ quasicoherentPushforward V.ι

/-- The unit `G ⟶ (V ↪ X)_*(G|_V)`. -/
def cechUnit (V : X.Opens) [QuasiCompact V.ι] [QuasiSeparated V.ι] : 𝟭 _ ⟶ cechObj V :=
  (qcohRestrictAdjunction V.ι).unit

/-- The underlying morphism of modules of `(cechUnit V).app G` is the unit of
`Scheme.Modules.restrictAdjunction V.ι` at the underlying module of `G`. -/
theorem cechUnit_app_hom (V : X.Opens) [QuasiCompact V.ι] [QuasiSeparated V.ι]
    (G : Scheme.QuasicoherentModules X) :
    ((cechUnit V).app G).hom = (Scheme.Modules.restrictAdjunction V.ι).unit.app G.obj :=
  qcohRestrictAdjunction_unit_app_hom V.ι G

/-- The restriction map `(V ↪ X)_*(G|_V) ⟶ (W ↪ X)_*(G|_W)` for `W ≤ V`. -/
def cechRestr {V W : X.Opens} [QuasiCompact V.ι] [QuasiSeparated V.ι] [QuasiCompact W.ι]
    [QuasiSeparated W.ι] (h : W ≤ V) : cechObj V ⟶ cechObj W where
  app G := ObjectProperty.homMk (restrictPushModMap h G.obj)
  naturality _ _ φ := (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map_injective
    (restrictPushModMap_naturality h φ.hom)

/-- The underlying morphism of modules of `(cechRestr h).app G` is `restrictPushModMap h G.obj`.
-/
theorem cechRestr_app_hom {V W : X.Opens} [QuasiCompact V.ι] [QuasiSeparated V.ι]
    [QuasiCompact W.ι] [QuasiSeparated W.ι] (h : W ≤ V) (G : Scheme.QuasicoherentModules X) :
    ((cechRestr h).app G).hom = restrictPushModMap h G.obj := rfl

/-- For `W ≤ V`, the unit `G ⟶ (V ↪ X)_*(G|_V)` followed by the restriction map to
`(W ↪ X)_*(G|_W)` is the unit `G ⟶ (W ↪ X)_*(G|_W)`. -/
@[reassoc]
theorem cechUnit_comp_cechRestr {V W : X.Opens} [QuasiCompact V.ι] [QuasiSeparated V.ι]
    [QuasiCompact W.ι] [QuasiSeparated W.ι] (h : W ≤ V) (G : Scheme.QuasicoherentModules X) :
    (cechUnit V).app G ≫ (cechRestr h).app G = (cechUnit W).app G :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map_injective (by
    show ((cechUnit V).app G).hom ≫ ((cechRestr h).app G).hom = ((cechUnit W).app G).hom
    rw [cechUnit_app_hom, cechUnit_app_hom, cechRestr_app_hom]
    exact restrictAdjunction_unit_comp_restrictPushModMap h G.obj)

variable {ι : Type u} (U : ι → X.Opens) [∀ i, QuasiCompact (U i).ι] [∀ i, QuasiSeparated (U i).ι]
  [∀ i j, QuasiCompact (U i ⊓ U j).ι] [∀ i j, QuasiSeparated (U i ⊓ U j).ι]

include U in
/-- The Čech diagram `(U_i)_*(G|_{U_i}) ⇉ (U_i ∩ U_j)_*(G|_{U_i ∩ U_j})`. -/
@[simps]
def cechIndex (G : Scheme.QuasicoherentModules X) :
    MulticospanIndex (MulticospanShape.prod ι) (Scheme.QuasicoherentModules X) where
  left := fun (i : ι) => (cechObj (U i)).obj G
  right := fun (p : ι × ι) => (cechObj (U p.1 ⊓ U p.2)).obj G
  fst := fun (p : ι × ι) => (cechRestr (V := U p.1) (W := U p.1 ⊓ U p.2) inf_le_left).app G
  snd := fun (p : ι × ι) => (cechRestr (V := U p.2) (W := U p.1 ⊓ U p.2) inf_le_right).app G

/-- **The Čech multifork** `G ⟶ (U_i)_*(G|_{U_i}) ⇉ (U_i ∩ U_j)_*(G|_{U_i ∩ U_j})`. -/
def cechMultifork (G : Scheme.QuasicoherentModules X) : Multifork (cechIndex U G) :=
  Multifork.ofι _ G (fun (i : ι) => (cechUnit (U i)).app G) (fun (p : ι × ι) =>
    (cechUnit_comp_cechRestr (V := U p.1) (W := U p.1 ⊓ U p.2) inf_le_left G).trans
      (cechUnit_comp_cechRestr (V := U p.2) (W := U p.1 ⊓ U p.2) inf_le_right G).symm)

end CechQcoh

/-! ### The integral transform preserves the Čech multifork -/

section CechLeftExact

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))

/-- `M ↦ pr_1^* M ⊗ K`, on quasi-coherent modules on `X` with values in all modules on
`X ×_R Y`. -/
abbrev pullbackTensorKernel :
    Scheme.QuasicoherentModules X.left ⥤ (pullback X.hom Y.hom).Modules :=
  (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
    Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨(pullback X.hom Y.hom).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
          (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj (K.obj))

/-- **`pr_1^*(−) ⊗ K` restricted to `pr_1^{-1}(U)` only sees the restriction to `U`.** -/
def pullbackTensorKernelRestrictIso (U : X.left.Opens) :
    pullbackTensorKernel R X Y K ⋙
        Scheme.Modules.restrictFunctor (pullback.fst X.hom Y.hom ⁻¹ᵁ U).ι ≅
      ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
          Scheme.Modules.restrictFunctor U.ι) ⋙
        Scheme.Modules.pullback (pullback.fst X.hom Y.hom ∣_ U) ⋙
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            ⟨(pullback.fst X.hom Y.hom ⁻¹ᵁ U).toScheme.presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _
                ((pullback.fst X.hom Y.hom ⁻¹ᵁ U).toScheme.presheaf)
                (forget₂ CommRingCat RingCat)
                ((pullback.fst X.hom Y.hom ⁻¹ᵁ U).toScheme.ringCatSheaf.2)⟩).obj
            (((Scheme.Modules.pullback (pullback.fst X.hom Y.hom ⁻¹ᵁ U).ι).obj K.obj))) :=
  Functor.isoWhiskerLeft (pullbackTensorKernel R X Y K)
      (Scheme.Modules.restrictFunctorIsoPullback (pullback.fst X.hom Y.hom ⁻¹ᵁ U).ι) ≪≫
    Functor.isoWhiskerLeft ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (pullback.fst X.hom Y.hom))
      (pullbackTensorLeftIso (pullback.fst X.hom Y.hom ⁻¹ᵁ U).ι K.obj) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι
      (Functor.isoWhiskerRight
        (Scheme.Modules.pullbackComp (pullback.fst X.hom Y.hom ⁻¹ᵁ U).ι
            (pullback.fst X.hom Y.hom) ≪≫
          Scheme.Modules.pullbackCongr (morphismRestrict_ι (pullback.fst X.hom Y.hom) U).symm ≪≫
          (Scheme.Modules.pullbackComp (pullback.fst X.hom Y.hom ∣_ U) U.ι).symm ≪≫
          Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
            (Scheme.Modules.pullback (pullback.fst X.hom Y.hom ∣_ U)))
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨(pullback.fst X.hom Y.hom ⁻¹ᵁ U).toScheme.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _
              ((pullback.fst X.hom Y.hom ⁻¹ᵁ U).toScheme.presheaf)
              (forget₂ CommRingCat RingCat)
              ((pullback.fst X.hom Y.hom ⁻¹ᵁ U).toScheme.ringCatSheaf.2)⟩).obj
          (((Scheme.Modules.pullback (pullback.fst X.hom Y.hom ⁻¹ᵁ U).ι).obj K.obj)))))

variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  {ι : Type u} (U : ι → X.left.Opens) [∀ i, QuasiCompact (U i).ι] [∀ i, QuasiSeparated (U i).ι]
  [∀ i j, QuasiCompact (U i ⊓ U j).ι] [∀ i j, QuasiSeparated (U i ⊓ U j).ι]

/-- **The restriction of the Čech multifork to a member of the family splits.** -/
def isLimitMapConeRestrictCechMultifork {D : Type*} [Category D] (k : ι)
    (Q : (U k).toScheme.Modules ⥤ D) (G : Scheme.QuasicoherentModules X.left) :
    IsLimit (Q.mapCone (((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι ⋙
      Scheme.Modules.restrictFunctor (U k).ι).mapCone (cechMultifork U G))) := by
  have : IsIso ((Scheme.Modules.restrictFunctor (U k).ι).map ((cechUnit (U k)).app G).hom) := by
    rw [cechUnit_app_hom]
    exact isIso_restrictFunctor_map_unit (U k) G.obj
  have : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U k).ι).map
      ((cechRestr (V := U i) (W := U k ⊓ U i) inf_le_right).app G).hom) := fun i =>
    isIso_restrictFunctor_map_restrictPushModMap _ le_rfl G.obj
  let e := asIso ((Scheme.Modules.restrictFunctor (U k).ι).map ((cechUnit (U k)).app G).hom)
  let et : ∀ i : ι, _ := fun i => asIso ((Scheme.Modules.restrictFunctor (U k).ι).map
      ((cechRestr (V := U i) (W := U k ⊓ U i) inf_le_right).app G).hom)
  have key : ∀ i : ι, e.inv ≫ (Scheme.Modules.restrictFunctor (U k).ι).map
      ((cechUnit (U i)).app G).hom = (Scheme.Modules.restrictFunctor (U k).ι).map
        ((cechRestr (V := U k) (W := U k ⊓ U i) inf_le_left).app G).hom ≫ (et i).inv := by
    intro i
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    simp only [e, et, asIso_hom]
    exact congrArg (Scheme.Modules.restrictFunctor (U k).ι).map (congrArg (fun φ => φ.hom)
      ((cechUnit_comp_cechRestr (V := U i) (W := U k ⊓ U i) inf_le_right G).trans
        (cechUnit_comp_cechRestr (V := U k) (W := U k ⊓ U i) inf_le_left G).symm))
  exact isLimitMapConeOfSplitMulticospan Q _ k e.inv (fun i => (et i).inv) e.hom_inv_id
    (fun i => (et i).hom_inv_id) key

/-- **The integral transform of a kernel carries the Čech multifork of a finite open cover to a
limit.** -/
def isLimitIntegralTransformCechMultifork (hU : IsOpenCover U)
    (G : Scheme.QuasicoherentModules X.left) :
    IsLimit ((quasicoherentIntegralTransform R X Y K).mapCone (cechMultifork U G)) := by
  let c := cechMultifork U G
  let ιY := (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι
  let V : ι → (pullback X.hom Y.hom).Opens := fun k => pullback.fst X.hom Y.hom ⁻¹ᵁ U k
  have hV : IsOpenCover V := by
    simpa [IsOpenCover, V, Scheme.Hom.preimage_iSup] using
      congrArg (fun W : X.left.Opens => pullback.fst X.hom Y.hom ⁻¹ᵁ W) hU
  have h0 : IsLimit ((pullbackTensorKernel R X Y K).mapCone c) :=
    isLimitOfIsLimitRestrict _ V hV fun k =>
      (IsLimit.mapConeEquiv (pullbackTensorKernelRestrictIso R X Y K (U k)).symm
          ((isLimitMapConeRestrictCechMultifork R X U k _ G).ofIsoLimit
            (Functor.mapConeMapCone c))).ofIsoLimit (Functor.mapConeMapCone c).symm
  have h1 : IsLimit ((pullbackTensorKernel R X Y K ⋙
      Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).mapCone c) :=
    (isLimitOfPreserves (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) h0).ofIsoLimit
      (Functor.mapConeMapCone c)
  have h2 : IsLimit ((quasicoherentIntegralTransform R X Y K ⋙ ιY).mapCone c) :=
    IsLimit.mapConeEquiv (quasicoherentIntegralTransformData R X Y K).comparison.symm h1
  exact isLimitOfReflects ιY (h2.ofIsoLimit (Functor.mapConeMapCone c).symm)

end CechLeftExact

end AlgebraicGeometry

end
