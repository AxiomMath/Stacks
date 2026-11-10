module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Properties
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.IdealSheafOfHomComap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderBiproducts
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.FunctorialityProj
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.ChartHom
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.AffineOpenSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# The direct image of the structure sheaf of a cyclic cover

Let `p : X ⟶ Z_S` be the cyclic cover `Spec_{Z_S}(Sym(L_S)/(φ - c))` of
`StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Construction`, for
`φ : Symⁿ L ≅ 𝒪_Z` and `n ≥ 1`. A local section of `Symⁱ L` is a homogeneous function of degree `i`
on the total space of `L`; pulling these back to `X` gives maps `(Symⁱ L)_S ⟶ p_* 𝒪_X`, and their
sum

`⨁_{i < n} (Symⁱ L)_S ⟶ p_* 𝒪_X`

is an isomorphism. Over a trivializing affine open `U = Spec A` of `Z`, with basis `s` of `L|_U`
and `f = φ(sⁿ)`, this is the statement that `(A ⊗_k S)[x]/(xⁿ - c f)` is free over `A ⊗_k S` on
`1, x, …, xⁿ⁻¹`, `sⁱ` going to `xⁱ`.

## Main definitions

* `Stacks.CyclicCover.symPowToCoverMap`: the map `(Symⁱ L)_S ⟶ p_* 𝒪_X`.
* `Stacks.CyclicCover.pushforwardDecomposition`: their sum over `i < n`.

## Main results

* `Stacks.CyclicCover.bijective_pushforwardDecomposition_app`: on sections over `U_S`, for `U` a
  trivializing affine open, the decomposition is bijective.
* `Stacks.CyclicCover.isIso_pushforwardDecomposition`: **`p_* 𝒪_X = ⨁_{i < n} (Symⁱ L)_S`.**

## References

* [Stacks Project, Tag 0CEH](https://stacks.math.columbia.edu/tag/0CEH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace Polynomial
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.CyclicCover

attribute [local instance] Abelian.hasFiniteBiproducts

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) {L : Z.Modules}
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] {n : ℕ}
  (φ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf)
  (S : Type u) [CommRing S] [Algebra k S] (c : S)

/-- Homogeneous functions are linear over the structure morphism. -/
theorem totalFunction_smul (i : ℕ) (W : Z.Opens) (a : Z.ringCatSheaf.obj.obj (op W))
    (x : ((situation f L).symmetricAlgebra.piece (i : ℤ)).val.obj (op W)) :
    (situation f L).totalFunction i W (a • x) =
      ((totalSpaceToBase f L).app W).hom a * (situation f L).totalFunction i W x := by
  rw [Stacks.LineBundle.Situation.totalFunction, (situation f L).algebraSheafIncl_smul]
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ rfl)
  exact congrArg (fun k => k.hom a)
    (Stacks.RelativeSpec.toBase_app (situation f L).relativeSpecSituation W).symm


/-- The degree-`i` piece `Symⁱ L(W) ⟶ Γ(X, (X ⟶ Z)⁻¹ W)` on sections: a local section goes to its
homogeneous function, pulled back to `X`. -/
def symPowToCoverApp (i : ℕ) (W : (Z.Opens)ᵒᵖ) :
    (((situation f L).symmetricAlgebra.piece (i : ℤ)).val.obj W) →ₗ[Z.ringCatSheaf.obj.obj W]
      (((Scheme.Modules.pushforward (coverFst f φ S c ≫ totalSpaceToBase f L)).obj
        (SheafOfModules.unit (cover f φ S c).ringCatSheaf)).val.obj W) where
  toFun x := ((coverFst f φ S c).app _).hom ((situation f L).totalFunction i W.unop x)
  map_add' x y := by
    simp only [(situation f L).totalFunction_add, map_add]
    rfl
  map_smul' a x := by
    simp only [totalFunction_smul f i W.unop a x, map_mul]
    rfl


/-- **The degree-`i` piece of `p_* 𝒪_X`**: `Symⁱ L ⟶ (X ⟶ Z)_* 𝒪_X`, a local section going to its
homogeneous function on `𝕃` pulled back to `X`. -/
def symPowToCover (i : ℕ) :
    (situation f L).symmetricAlgebra.piece (i : ℤ) ⟶
      (Scheme.Modules.pushforward (coverFst f φ S c ≫ totalSpaceToBase f L)).obj
        (SheafOfModules.unit (cover f φ S c).ringCatSheaf) where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (symPowToCoverApp f φ S c i W).toAddMonoidHom
      naturality := fun {W W'} g => by
        ext x
        have h1 := (situation f L).totalFunction_map i (leOfHom g.unop) x
          ((Opens.map (totalSpaceToBase f L).base).map g.unop).op
        have h2 := ConcreteCategory.congr_hom
          ((coverFst f φ S c).naturality ((Opens.map (totalSpaceToBase f L).base).map g.unop).op)
          ((situation f L).totalFunction i W.unop x)
        change ((coverFst f φ S c).app _).hom ((situation f L).totalFunction i W'.unop
          (((situation f L).symmetricAlgebra.piece (i : ℤ)).val.map g x)) = _
        rw [show g = (homOfLE (leOfHom g.unop)).op from rfl, ← h1]
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
        refine h2.trans ?_
        rfl }
    (fun W a x => (symPowToCoverApp f φ S c i W).map_smul a x)


/-- The degree-`i` piece `(Symⁱ L)_S ⟶ p_* 𝒪_X` over `Z_S`, adjoint to
`Stacks.CyclicCover.symPowToCover`. -/
def symPowToCoverMap (i : ℕ) :
    (Scheme.Modules.pullback (baseChangeFst f S)).obj
        ((situation f L).symmetricAlgebra.piece (i : ℤ)) ⟶
      (Scheme.Modules.pushforward (coverMap f φ S c)).obj
        (SheafOfModules.unit (cover f φ S c).ringCatSheaf) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (baseChangeFst f S)).homEquiv _ _).symm
    (symPowToCover f φ S c i ≫
      (Scheme.Modules.pushforwardCongr (coverMap_fst f φ S c).symm).hom.app _ ≫
      (Scheme.Modules.pushforwardComp (coverMap f φ S c) (baseChangeFst f S)).inv.app _)

variable (n) in
/-- **The decomposition `⨁_{i < n} (Symⁱ L)_S ⟶ p_* 𝒪_X`.** -/
def pushforwardDecomposition :
    (⨁ fun i : Fin n => (Scheme.Modules.pullback (baseChangeFst f S)).obj
        ((situation f L).symmetricAlgebra.piece ((i : ℕ) : ℤ))) ⟶
      (Scheme.Modules.pushforward (coverMap f φ S c)).obj
        (SheafOfModules.unit (cover f φ S c).ringCatSheaf) :=
  biproduct.desc fun i => symPowToCoverMap f φ S c i


/-- Functions on an open `W` identified with a ring `R` through an isomorphism `W ≅ Spec R`. -/
def openSectionsEquivOfIso {X : Scheme.{u}} (W : X.Opens) {R : CommRingCat.{u}}
    (e : W.toScheme ≅ Spec R) : Γ(X, W) ≃+* R :=
  (W.topIso.symm ≪≫ Scheme.Γ.mapIso e.symm.op ≪≫ Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv

/-- For `e : W ≅ Spec R`, the map `Γ(X, W) ⟶ Γ(Spec R, ⊤)` induced by `e⁻¹` is the restriction
along `e⁻¹ ≫ W.ι`. -/
theorem topIso_inv_appTop {X : Scheme.{u}} (W : X.Opens) {R : CommRingCat.{u}}
    (e : W.toScheme ≅ Spec R) :
    W.topIso.inv ≫ e.inv.appTop = (e.inv ≫ W.ι).appLE W ⊤ (by simp) := by
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ _ (by simp) (by simp)]
  congr 1
  simp only [Scheme.Opens.topIso, Scheme.Hom.appLE]
  refine Eq.trans ?_ (X.presheaf.map_comp _ _)
  rfl

/-- `Stacks.CyclicCover.openSectionsEquivOfIso` sends `y` to the global function `e⁻¹ ^* y` on
`Spec R`, read in `R`. -/
theorem openSectionsEquivOfIso_apply {X : Scheme.{u}} (W : X.Opens) {R : CommRingCat.{u}}
    (e : W.toScheme ≅ Spec R) (y : Γ(X, W)) :
    openSectionsEquivOfIso W e y = (Scheme.ΓSpecIso R).hom (e.inv.appTop (W.topIso.inv y)) := rfl

/-- For an affine open `W`, the identification through `IsAffineOpen.isoSpec` is the identity of
`Γ(X, W)`. -/
theorem openSectionsEquivOfIso_isoSpec {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    (y : Γ(X, W)) : openSectionsEquivOfIso W hW.isoSpec y = y := by
  rw [openSectionsEquivOfIso_apply, IsAffineOpen.isoSpec_inv_appTop, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id]
  rfl

/-- If `g : X ⟶ Y` maps `W ≅ Spec R` into `W' ≅ Spec R'` through `Spec φ`, then under these
identifications pulling back functions along `g` is `φ`. -/
theorem openSectionsEquivOfIso_appLE {X Y : Scheme.{u}} (g : X ⟶ Y) {W : X.Opens} {W' : Y.Opens}
    (h : W ≤ g ⁻¹ᵁ W') {R R' : CommRingCat.{u}} (e : W.toScheme ≅ Spec R)
    (e' : W'.toScheme ≅ Spec R') (φ : R' ⟶ R)
    (hφ : e.hom ≫ Spec.map φ ≫ e'.inv ≫ W'.ι = W.ι ≫ g) (y : Γ(Y, W')) :
    openSectionsEquivOfIso W e (g.appLE W' W h y) = φ (openSectionsEquivOfIso W' e' y) := by
  have key : ∀ (a b : Spec R ⟶ Y) (_ : a = b) h1 h2, a.appLE W' ⊤ h1 = b.appLE W' ⊤ h2 := by
    rintro _ _ rfl _ _; rfl
  have hφ' : e.inv ≫ W.ι ≫ g = Spec.map φ ≫ e'.inv ≫ W'.ι := by
    rw [← hφ, Iso.inv_hom_id_assoc]
  have H : g.appLE W' W h ≫ W.topIso.inv ≫ e.inv.appTop ≫ (Scheme.ΓSpecIso R).hom =
      W'.topIso.inv ≫ e'.inv.appTop ≫ (Scheme.ΓSpecIso R').hom ≫ φ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc (W.topIso.inv), topIso_inv_appTop,
      ← Category.assoc (W'.topIso.inv), topIso_inv_appTop, ← Category.assoc, ← Category.assoc,
      Scheme.Hom.appLE_comp_appLE]
    congr 1
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE (Spec.map φ) (e'.inv ≫ W'.ι) W' ⊤ _ _ _).symm
    exact key _ _ (by simpa using hφ') _ _
  exact congrArg (fun t => t.hom y) H


section Sections

variable (U : Z.affineOpens) (b : Module.Basis PUnit.{u + 1} Γ(Z, U.1) Γ(L, U.1))

/-- For `M` free of rank one over `R` on `ε 1`, every element of the image of a linear map out of
`S ⊗_R M` is a multiple of the image of `1 ⊗ ε 1`. -/
theorem exists_eq_smul_extendScalars {R S : Type u} [CommRing R] [CommRing S] (α : R →+* S)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S} (ψ : (ModuleCat.extendScalars α).obj M ⟶ N)
    (ε : ModuleCat.of R R ≅ M) (w : (ModuleCat.extendScalars α).obj M) :
    ∃ q : S, ψ w = q • ψ ((1 : S) ⊗ₜ[R, α] ε.hom (1 : R)) := by
  let Λ := (ModuleCat.ExtendScalars.objSelfIso α).inv ≫ (ModuleCat.extendScalars α).map ε.hom ≫ ψ
  refine ⟨(ModuleCat.ExtendScalars.objSelfIso α).hom ((ModuleCat.extendScalars α).map ε.inv w), ?_⟩
  have key : ∀ z, (ModuleCat.extendScalars α).map ε.hom ((ModuleCat.extendScalars α).map ε.inv z)
      = z := fun z => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    rfl
  have h1 : Λ ((ModuleCat.ExtendScalars.objSelfIso α).hom ((ModuleCat.extendScalars α).map ε.inv w))
      = ψ w := by
    change ψ ((ModuleCat.extendScalars α).map ε.hom ((ModuleCat.ExtendScalars.objSelfIso α).inv
      ((ModuleCat.ExtendScalars.objSelfIso α).hom ((ModuleCat.extendScalars α).map ε.inv w)))) = _
    rw [Iso.hom_inv_id_apply, key]
  have h2 : ∀ s : S, Λ s = s • Λ 1 := fun s => by
    rw [← (ConcreteCategory.hom Λ).map_smul, smul_eq_mul, mul_one]
  have h3 : Λ 1 = ψ ((1 : S) ⊗ₜ[R, α] ε.hom (1 : R)) :=
    congrArg ψ ((congrArg ((ModuleCat.extendScalars α).map ε.hom)
      (ModuleCat.ExtendScalars.objSelfIso_inv_apply α 1)).trans
        (ModuleCat.ExtendScalars.map_tmul α ε.hom 1 1))
  rw [← h1, h2, h3]

/-- **`Q[x]/(xⁿ - u)` is free on `1, x, …, xⁿ⁻¹`**, as a bijectivity statement valid also over the
zero ring. -/
theorem bijective_sum_root_pow {Q : Type u} [CommRing Q] (u : Q) {n : ℕ} (hn : n ≠ 0) :
    Function.Bijective (fun a : Fin n → Q => ∑ i, algebraMap Q (AdjoinRoot (Polynomial.X ^ n - C u))
      (a i) * AdjoinRoot.root (Polynomial.X ^ n - C u) ^ (i : ℕ)) := by
  rcases subsingleton_or_nontrivial Q with hQ | hQ
  · have : Subsingleton (AdjoinRoot (Polynomial.X ^ n - C u)) := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
      rw [Subsingleton.elim p q]
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · let e := (rootPowerBasis u hn).basis.reindex (finCongr (rootPowerBasis_dim u hn))
    have he : ∀ i, e i = AdjoinRoot.root _ ^ (i : ℕ) := fun i => by
      simp [e, rootPowerBasis, AdjoinRoot.powerBasis'_gen]
      rfl
    convert e.equivFun.symm.bijective using 1
    funext a
    simp [Module.Basis.equivFun_symm_apply, he, Algebra.smul_def]

/-- The functions on `p⁻¹(U_S)` are the chart ring `(A ⊗_k S)[x]/(xⁿ - c f)`. -/
def coverSectionsEquiv :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    Γ(cover f φ S c, coverMap f φ S c ⁻¹ᵁ baseChangeOpen f S U.1) ≃+*
      chartRing k n (chartCoeff f φ U b) c :=
  letI := (sectionsStructure f U.1).hom.toAlgebra
  openSectionsEquivOfIso _ (Scheme.isoOfEq _ (preimage_baseChangeOpen f φ U S c) ≪≫
    coverOpenIso f φ U b S c)

/-- The functions on `U_S` are `A ⊗_k S`. -/
def baseChangeSectionsEquiv :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    Γ(baseChange f S, baseChangeOpen f S U.1) ≃+* (Γ(Z, U.1) ⊗[k] S) :=
  letI := (sectionsStructure f U.1).hom.toAlgebra
  openSectionsEquivOfIso _ (baseChangeOpenIso f U S)

/-- Under the identifications of `Stacks.CyclicCover.coverSectionsEquiv` and
`Stacks.CyclicCover.baseChangeSectionsEquiv`, pulling back functions along `p` is the algebra map
`A ⊗_k S ⟶ (A ⊗_k S)[x]/(xⁿ - c f)`. -/
theorem coverSectionsEquiv_app (y : Γ(baseChange f S, baseChangeOpen f S U.1)) :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    coverSectionsEquiv f φ S c U b ((coverMap f φ S c).app _ y) =
      algebraMap _ _ (baseChangeSectionsEquiv f S U y) := by
  let := (sectionsStructure f U.1).hom.toAlgebra
  rw [← Scheme.Hom.appLE_eq_app]
  refine openSectionsEquivOfIso_appLE _ _ _ _ (CommRingCat.ofHom (algebraMap _ _)) ?_ y
  have hw : (Scheme.isoOfEq _ (preimage_baseChangeOpen f φ U S c) ≪≫ coverOpenIso f φ U b S c).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Γ(Z, U.1) ⊗[k] S)
        (chartRing k n (chartCoeff f φ U b) c))) =
      (coverMap f φ S c ∣_ baseChangeOpen f S U.1) ≫ (baseChangeOpenIso f U S).hom :=
    (coverMapArrowIso f φ U b S c).hom.w
  rw [← Category.assoc, hw, Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]

/-- Under the identifications of `Stacks.CyclicCover.coverSectionsEquiv` and
`Stacks.CyclicCover.chartOpenIso`, pulling back functions along `X ⟶ 𝕃` from the chart is
`Stacks.CyclicCover.chartLeft`. -/
theorem coverSectionsEquiv_appLE (t : Γ(totalSpace f L, chartOpen f (L := L) U))
    (h : coverMap f φ S c ⁻¹ᵁ baseChangeOpen f S U.1 ≤ coverFst f φ S c ⁻¹ᵁ chartOpen f U) :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    coverSectionsEquiv f φ S c U b ((coverFst f φ S c).appLE _ _ h t) =
      chartLeft k n (chartCoeff f φ U b) c (openSectionsEquivOfIso _ (chartOpenIso f U b) t) := by
  let := (sectionsStructure f U.1).hom.toAlgebra
  refine openSectionsEquivOfIso_appLE _ _ _ _ (CommRingCat.ofHom (chartLeft k n _ c)) ?_ t
  rw [Iso.trans_hom, Category.assoc, coverOpenIso, IsPullback.isoIsPullback_hom_fst_assoc,
    Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

/-- The identification of the functions on the chart with `A[T]` through
`Stacks.CyclicCover.chartOpenIso` inverts `polynomialSectionsRingEquiv`. -/
theorem openSectionsEquivOfIso_chartOpenIso (q : Γ(Z, U.1)[X]) :
    openSectionsEquivOfIso _ (chartOpenIso f U b)
      ((situation f L).polynomialSectionsRingEquiv U b q) = q := by
  have h := openSectionsEquivOfIso_appLE (𝟙 _) (le_refl (chartOpen f (L := L) U))
    (chartOpenIso f U b) (isAffineOpen_chartOpen f U).isoSpec
    (CommRingCat.ofHom ((situation f L).polynomialSectionsRingEquiv U b).symm.toRingHom)
    (by rw [chartOpenIso_hom, ← IsAffineOpen.isoSpec_hom (isAffineOpen_chartOpen f U),
      Category.assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]; simp)
    ((situation f L).polynomialSectionsRingEquiv U b q)
  have h1 : Scheme.Hom.appLE (𝟙 (totalSpace f L)) (chartOpen f (L := L) U)
      (chartOpen f (L := L) U) le_rfl = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (totalSpace f L).presheaf.map_id _
  rw [h1] at h
  refine h.trans ?_
  rw [openSectionsEquivOfIso_isoSpec]
  exact ((situation f L).polynomialSectionsRingEquiv U b).symm_apply_apply q


/-- The functions `sⁱ` of degree `i` on the chart are the monomials `Tⁱ`. -/
theorem totalFunction_basisPow (i : ℕ) :
    (situation f L).totalFunction i U.1 (basisPow (n := i) f U b) =
      (situation f L).polynomialSectionsRingEquiv U b (Polynomial.X ^ i) := by
  rw [basisPow, ← (situation f L).symSectionsRingEquiv_coe]
  change _ = (situation f L).symSectionsRingEquiv U
    (((situation f L).polynomialAlgEquiv U b).symm (Polynomial.X ^ i))
  congr 1
  rw [AlgEquiv.eq_symm_apply, map_pow, (situation f L).polynomialAlgEquiv_ι]

/-- The homogeneous function of `g • sⁱ` is the monomial `g Tⁱ`. -/
private theorem totalFunction_smul_basisPow (i : ℕ) (g : Γ(Z, U.1)) :
    (situation f L).totalFunction i U.1
        (id (α := Z.ringCatSheaf.obj.obj (op U.1)) g • basisPow (n := i) f U b) =
      (situation f L).polynomialSectionsRingEquiv U b (monomial i g) := by
  rw [totalFunction_smul, totalFunction_basisPow, ← C_mul_X_pow_eq_monomial, map_mul,
    (situation f L).polynomialSectionsRingEquiv_C]
  rfl

/-- Every section of `Symⁱ L` over the trivializing open `U` is a multiple of `sⁱ`. -/
theorem exists_eq_smul_basisPow (i : ℕ)
    (x : ((situation f L).symmetricAlgebra.piece (i : ℤ)).val.obj (op U.1)) :
    ∃ g : Γ(Z, U.1), x = id (α := Z.ringCatSheaf.obj.obj (op U.1)) g • basisPow f U b := by
  obtain ⟨g, hg⟩ := ((situation f L).exists_totalFunction_iff U b i _).mp ⟨x, rfl⟩
  exact ⟨g, totalFunction_injective f U (by rw [← hg, totalFunction_smul_basisPow])⟩

/-- On the pullback of a section `x` of `Symⁱ L` over `U`, the map
`Stacks.CyclicCover.symPowToCoverMap` gives the pullback to `p⁻¹(U_S)` of the homogeneous function
of `x`. -/
theorem symPowToCoverMap_app (i : ℕ) (x : ((situation f L).symmetricAlgebra.piece (i : ℤ)).val.obj
    (op U.1)) :
    (symPowToCoverMap f φ S c i).app (baseChangeOpen f S U.1)
      (Scheme.Modules.pullbackSection (baseChangeFst f S) _ U.1 _ le_rfl x) =
    (coverFst f φ S c).appLE (chartOpen f U) (coverMap f φ S c ⁻¹ᵁ baseChangeOpen f S U.1)
      (by rw [preimage_baseChangeOpen]) ((situation f L).totalFunction i U.1 x) := by
  rw [symPowToCoverMap]
  refine (Stacks.AlgebraicGeometry.ProjectiveDeformation.homEquiv_symm_app_pullbackSection
    _ _ _ _ _ _).trans ?_
  change (cover f φ S c).presheaf.map _ ((cover f φ S c).presheaf.map _
    (((coverFst f φ S c).app _).hom ((situation f L).totalFunction i U.1 x))) = _
  rw [← ConcreteCategory.comp_apply]
  exact (ConcreteCategory.congr_hom ((cover f φ S c).presheaf.map_comp _ _) _).symm.trans rfl

/-- The pullback of `sⁱ` to `U_S`. -/
def basisPowPullback (i : ℕ) : Γ((Scheme.Modules.pullback (baseChangeFst f S)).obj
    ((situation f L).symmetricAlgebra.piece (i : ℤ)), baseChangeOpen f S U.1) :=
  Scheme.Modules.pullbackSection (baseChangeFst f S) _ U.1 _ le_rfl (basisPow f U b)

/-- In the chart ring `(A ⊗_k S)[x]/(xⁿ - c f)`, the image of `q` times the pullback of `sⁱ` is
`q xⁱ`. -/
theorem coverSectionsEquiv_symPowToCoverMap (i : ℕ)
    (q : Γ(baseChange f S, baseChangeOpen f S U.1)) :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    coverSectionsEquiv f φ S c U b
      ((symPowToCoverMap f φ S c i).app (baseChangeOpen f S U.1) (q • basisPowPullback f S U b i)) =
      algebraMap _ _ (baseChangeSectionsEquiv f S U q) * AdjoinRoot.root _ ^ i := by
  let := (sectionsStructure f U.1).hom.toAlgebra
  rw [Scheme.Modules.Hom.app_smul]
  change coverSectionsEquiv f φ S c U b ((coverMap f φ S c).app _ q *
    id (α := Γ(cover f φ S c, coverMap f φ S c ⁻¹ᵁ baseChangeOpen f S U.1))
      ((symPowToCoverMap f φ S c i).app (baseChangeOpen f S U.1) (basisPowPullback f S U b i))) = _
  rw [map_mul]
  refine congrArg₂ (· * ·) (coverSectionsEquiv_app f φ S c U b q) ?_
  rw [basisPowPullback, symPowToCoverMap_app, id,
    coverSectionsEquiv_appLE, totalFunction_basisPow, openSectionsEquivOfIso_chartOpenIso, map_pow,
    chartLeft_X]

/-- For `U` an affine open of `Z`, the open `U_S` of `Z_S` is affine. -/
theorem isAffineOpen_baseChangeOpen : IsAffineOpen (baseChangeOpen f S U.1) :=
  let := (sectionsStructure f U.1).hom.toAlgebra
  IsAffine.of_isIso (baseChangeOpenIso f U S).hom

/-- Every section of `(Symⁱ L)_S` over `U_S` is a multiple of the pullback of `sⁱ`. -/
theorem exists_eq_smul_basisPowPullback (i : ℕ)
    (y : Γ((Scheme.Modules.pullback (baseChangeFst f S)).obj
      ((situation f L).symmetricAlgebra.piece (i : ℤ)), baseChangeOpen f S U.1)) :
    ∃ q : Γ(baseChange f S, baseChangeOpen f S U.1), y = q • basisPowPullback f S U b i := by
  have := (situation f L).isQuasicoherent_symmetricAlgebra_piece i
  let F : Z.Modules := (situation f L).symmetricAlgebra.piece (i : ℤ)
  have hinj : Function.Injective (LinearMap.toSpanSingleton Γ(Z, U.1) Γ(F, U.1)
      (basisPow (n := i) f U b)) := by
    refine (injective_iff_map_eq_zero _).2 fun g hg => ?_
    have h := congrArg ((situation f L).totalFunction i U.1) hg
    have h0 : (situation f L).totalFunction i U.1 0 = 0 := by
      have := (situation f L).totalFunction_add i U.1 0 0
      rw [add_zero] at this
      linear_combination -this
    change (situation f L).totalFunction i U.1 (id (α := Z.ringCatSheaf.obj.obj (op U.1)) g •
      basisPow (n := i) f U b) = (situation f L).totalFunction i U.1 0 at h
    rw [totalFunction_smul_basisPow, h0,
      ← map_zero ((situation f L).polynomialSectionsRingEquiv U b),
      ((situation f L).polynomialSectionsRingEquiv U b).injective.eq_iff,
      monomial_eq_zero_iff] at h
    exact h
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton Γ(Z, U.1) Γ(F, U.1)
      (basisPow (n := i) f U b)) := fun x =>
    (exists_eq_smul_basisPow f U b i x).imp fun _ hg => hg.symm
  let ε : ModuleCat.of Γ(Z, U.1) Γ(Z, U.1) ≅ ModuleCat.of Γ(Z, U.1) Γ(F, U.1) :=
    (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toModuleIso
  obtain ⟨w, rfl⟩ : ∃ w, (affinePullbackSectionsBaseChangeIso (baseChangeFst f S) F U.2
      (isAffineOpen_baseChangeOpen f S U) le_rfl).hom w = y :=
    ⟨_, ConcreteCategory.congr_hom (Iso.inv_hom_id (affinePullbackSectionsBaseChangeIso
      (baseChangeFst f S) F U.2 (isAffineOpen_baseChangeOpen f S U) le_rfl)) y⟩
  obtain ⟨q, hq⟩ := exists_eq_smul_extendScalars
    ((baseChangeFst f S).appLE U.1 (baseChangeOpen f S U.1) le_rfl).hom
    (affinePullbackSectionsBaseChangeIso (baseChangeFst f S) F U.2
      (isAffineOpen_baseChangeOpen f S U) le_rfl).hom ε w
  refine ⟨q, hq.trans ?_⟩
  have h1 := affinePullbackSectionsBaseChangeIso_one_tmul (baseChangeFst f S) F U.2
    (isAffineOpen_baseChangeOpen f S U) le_rfl (basisPow (n := i) f U b)
  have h2 : ε.hom (1 : Γ(Z, U.1)) = basisPow (n := i) f U b := by
    change (1 : Γ(Z, U.1)) • (show Γ(F, U.1) from basisPow (n := i) f U b) = _
    exact one_smul _ _
  rw [h2, h1]
  rfl

variable (n) in
include b in
/-- **Over a trivializing affine open the decomposition is bijective on sections.** -/
theorem bijective_pushforwardDecomposition_app (hn : n ≠ 0) :
    Function.Bijective ((pushforwardDecomposition f n φ S c).app (baseChangeOpen f S U.1)) := by
  let := (sectionsStructure f U.1).hom.toAlgebra
  let M := fun i : Fin n => (Scheme.Modules.pullback (baseChangeFst f S)).obj
    ((situation f L).symmetricAlgebra.piece ((i : ℕ) : ℤ))
  let Ψ := (pushforwardDecomposition f n φ S c).app (baseChangeOpen f S U.1)
  have hι : ∀ (i : Fin n) y, Ψ ((biproduct.ι M i).app (baseChangeOpen f S U.1) y) =
      (symPowToCoverMap f φ S c i).app (baseChangeOpen f S U.1) y := fun i y => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, pushforwardDecomposition,
      biproduct.ι_desc]
  have hsum : ∀ (g : Fin n → ((⨁ M) ⟶ (⨁ M))) x, ((∑ i, g i).app (baseChangeOpen f S U.1)) x =
      ∑ i, (g i).app (baseChangeOpen f S U.1) x := by
    intro g x
    let A : ((⨁ M) ⟶ (⨁ M)) →+ (Γ(⨁ M, baseChangeOpen f S U.1) →+ Γ(⨁ M, baseChangeOpen f S U.1)) :=
      { toFun := fun t => (t.app (baseChangeOpen f S U.1)).hom
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact (congrArg (fun F => F x) (map_sum A g Finset.univ)).trans
      (AddMonoidHom.finsetSum_apply _ _ _)
  have htot : ∀ x, x = ∑ i, (biproduct.ι M i).app (baseChangeOpen f S U.1)
      ((biproduct.π M i).app (baseChangeOpen f S U.1) x) := fun x => by
    have h := congrArg (fun t => t.app (baseChangeOpen f S U.1) x) (biproduct.total (f := M))
    simp only at h
    rw [hsum] at h
    exact h.symm
  have hΨ : ∀ x, Ψ x = ∑ i : Fin n, (symPowToCoverMap f φ S c i).app (baseChangeOpen f S U.1)
      ((biproduct.π M i).app (baseChangeOpen f S U.1) x) := fun x => by
    conv_lhs => rw [htot x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hι i _
  have hB := bijective_sum_root_pow (chartCoeff f φ U b ⊗ₜ[k] c) hn
  refine ⟨(injective_iff_map_eq_zero Ψ.hom).2 fun x hx => ?_, fun s => ?_⟩
  · choose q hq using fun i : Fin n => exists_eq_smul_basisPowPullback f S U b i
      ((biproduct.π M i).app (baseChangeOpen f S U.1) x)
    have h0 : (fun i => baseChangeSectionsEquiv f S U (q i)) = 0 := by
      apply hB.1
      simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
      have h := congrArg (coverSectionsEquiv f φ S c U b) hx
      rw [hΨ] at h
      refine Eq.trans ?_ ((map_sum (coverSectionsEquiv f φ S c U b) _ Finset.univ).symm.trans
        (h.trans (map_zero (coverSectionsEquiv f φ S c U b))))
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hq i, coverSectionsEquiv_symPowToCoverMap]
    rw [htot x]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hqi : q i = 0 := (baseChangeSectionsEquiv f S U).injective
      ((congrFun h0 i).trans (map_zero _).symm)
    rw [hq i, hqi, zero_smul, map_zero]
  · obtain ⟨a, ha⟩ := hB.2 (coverSectionsEquiv f φ S c U b s)
    refine ⟨∑ i, (biproduct.ι M i).app (baseChangeOpen f S U.1)
      ((baseChangeSectionsEquiv f S U).symm (a i) • basisPowPullback f S U b i), ?_⟩
    apply (coverSectionsEquiv f φ S c U b).injective
    rw [← ha]
    refine (congrArg _ (map_sum Ψ.hom _ _)).trans ?_
    refine (map_sum (coverSectionsEquiv f φ S c U b) _ _).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hι, coverSectionsEquiv_symPowToCoverMap, RingEquiv.apply_symm_apply]

end Sections

variable (n) in
/-- **`p_* 𝒪_X = ⨁_{i < n} (Symⁱ L)_S`.** -/
theorem isIso_pushforwardDecomposition (hn : n ≠ 0) :
    IsIso (pushforwardDecomposition f n φ S c) := by
  have := isFinite_coverMap f φ S c hn
  have : ∀ i : Fin n, ((Scheme.Modules.pullback (baseChangeFst f S)).obj
      ((situation f L).symmetricAlgebra.piece ((i : ℕ) : ℤ))).IsQuasicoherent := fun i => by
    have := (situation f L).isQuasicoherent_symmetricAlgebra_piece i
    exact isQuasicoherent_modulesPullbackObj _ _
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover _
    (fun U : TrivialOpen L => baseChangeOpen f S U.1.1)
    (iSup_baseChangeOpen_trivialOpen f (L := L) S) (fun U => isAffineOpen_baseChangeOpen f S U.1)
    fun U => ?_
  obtain ⟨b⟩ := U.2
  exact bijective_pushforwardDecomposition_app f n φ S c U.1 b hn

end Stacks.CyclicCover

end
