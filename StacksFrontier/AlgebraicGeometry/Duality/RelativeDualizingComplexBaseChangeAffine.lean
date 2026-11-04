module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexSpecGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseChangeSquare

/-!
# Base change of the diagonal generator over affine schemes

Let `f : X ⟶ S` be flat and locally of finite presentation with `X`, `S` affine, `g : S' ⟶ S`
with `S'` affine, and `X'` with `g' : X' ⟶ X`, `f' : X' ⟶ S'` the base change. Write
`A = Γ(X, 𝒪_X)`, `R = Γ(S, 𝒪_S)` and `R' = Γ(S', 𝒪_{S'})`, so that `X' ≅ Spec(A ⊗_R R')`.

Let `(K, ξ)` be a pair on a diagonal open `W` of `f`, with `K` having quasi-coherent cohomology
and `RΓ(X, K)` a relative dualizing complex for `R → A`, and let `W'` be a diagonal open of `f'`
with `w : W' ⟶ W` the restriction of `g' × g'`. If `ξ` generates `Hom(Δ_*𝒪_X, L pr₁^*K|_W)` under
precomposition by endomorphisms of `Δ_*𝒪_X`, then so does its derived base change
`Δ'_*𝒪_{X'} ≅ Lw^*Δ_*𝒪_X ⟶ Lw^* L pr₁^*K|_W ≅ L pr₁^* L(g')^*K|_{W'}`, for any choice of the two
identifications.

The proof extends `ξ` from `W` to the diagonal open `Spec(A ⊗_R A)` of all of `X ×_S X` (excision,
`Δ_*𝒪_X` being supported on the diagonal), applies the "moreover" clause of Stacks 0E2F there
(`ofSpec_isPostcompGenerator_baseChange`), and restricts back to `W'`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.nonempty_derivedPullback_isoSpec_inv_iso`: on an affine scheme an
  object with quasi-coherent cohomology is the sheaf associated to its derived sections.
* `AlgebraicGeometry.Scheme.Hom.isoSpecTensor`: `X' ≅ Spec(A ⊗_R R')`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace AlgebraicGeometry.Scheme.Hom

/-! ### Affine identifications -/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `f.appLE ⊤ ⊤` as an `Γ(S, ⊤)`-algebra structure on `Γ(X, ⊤)`. -/
abbrev affineSectionsAlgebra : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra

/-- Through `X ≅ Spec Γ(X, ⊤)` and `S ≅ Spec Γ(S, ⊤)`, the morphism `f` is `Spec` of the algebra
map `Γ(S, ⊤) → Γ(X, ⊤)`. -/
theorem isoSpec_hom_specMap_algebraMap [IsAffine X] [IsAffine S] :
    letI := affineSectionsAlgebra f
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤))) =
      f ≫ S.isoSpec.hom := by
  let := affineSectionsAlgebra f
  have h : CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)) = f.appTop :=
    appLE_top_top f le_top
  rw [h, Scheme.isoSpec_hom_naturality]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **On an affine scheme, an object with quasi-coherent cohomology is the sheaf associated to its
derived sections** (Stacks 06Z0), read on `Spec Γ(X, ⊤)` through `X ≅ Spec Γ(X, ⊤)`. -/
theorem nonempty_derivedPullback_isoSpec_inv_iso [IsAffine X] (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent) :
    Nonempty ((derivedPullback X.isoSpec.inv.toLRSHom.toShHom).obj K ≅
      (tilde.functor Γ(X, ⊤)).mapDerivedCategory.obj ((derivedSectionsUnbounded X ⊤).obj K)) := by
  let hU := isAffineOpen_top X
  obtain ⟨e₁⟩ := hU.nonempty_iso_derivedTilde_derivedSectionsSpec K hK
  obtain ⟨e₂⟩ := hU.nonempty_iso_derivedSectionsSpec K
  have h : X.isoSpec.inv = hU.isoSpec.inv ≫ (⊤ : X.Opens).ι := by
    rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.fromSpec_top]
  refine ⟨Scheme.derivedPullbackCongrObj h K ≪≫ (Scheme.derivedPullbackCompObj _ _ K).symm ≪≫
    (derivedPullback hU.isoSpec.inv.toLRSHom.toShHom).mapIso
      (((Scheme.Modules.derivedRestrictIsoDerivedPullback (⊤ : X.Opens).ι).app K).symm ≪≫ e₁ ≪≫
        (Scheme.pushforwardInvIsoDerivedPullback hU.isoSpec).app _) ≪≫
    (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackHomInvIso
      (Scheme.toRingedSpaceIso hU.isoSpec)).app _ ≪≫
    (tilde.functor Γ(X, ⊤)).mapDerivedCategory.mapIso e₂⟩

/-! ### The base change of an affine scheme over an affine scheme -/

variable {S' X' : Scheme.{u}} {f} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  (hpb : IsPullback g' f' f g) [IsAffine X] [IsAffine S] [IsAffine S']

/-- **`X' ≅ Spec(A ⊗_R R')`** for the base change `X'` of `X = Spec A` along
`S' = Spec R' ⟶ Spec R`,
with `A = Γ(X, ⊤)`, `R = Γ(S, ⊤)` and `R' = Γ(S', ⊤)`. -/
def isoSpecTensor :
    letI := affineSectionsAlgebra f
    letI := affineSectionsAlgebra g
    X' ≅ Spec (CommRingCat.of (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤))) :=
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  hpb.isoPullback ≪≫
    asIso (pullback.map f g _ _ X.isoSpec.hom S'.isoSpec.hom S.isoSpec.hom
      (isoSpec_hom_specMap_algebraMap f).symm (isoSpec_hom_specMap_algebraMap g).symm) ≪≫
    pullbackSpecIso Γ(S, ⊤) Γ(X, ⊤) Γ(S', ⊤)

/-- Through `isoSpecTensor` and `S' ≅ Spec Γ(S', ⊤)`, the morphism `f'` is `Spec` of the algebra
map `Γ(S', ⊤) → Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)`. -/
theorem isoSpecTensor_hom_snd :
    letI := affineSectionsAlgebra f
    letI := affineSectionsAlgebra g
    (isoSpecTensor hpb).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S', ⊤) (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)))) =
      f' ≫ S'.isoSpec.hom := by
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  have h : CommRingCat.ofHom (algebraMap Γ(S', ⊤) (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤))) =
      CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
        Γ(S', ⊤) →ₐ[Γ(S, ⊤)] Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)) :
          Γ(S', ⊤) →+* Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)) := rfl
  simp only [isoSpecTensor, Iso.trans_hom, asIso_hom, Category.assoc, h]
  rw [pullbackSpecIso_hom_snd, pullback.lift_snd, ← Category.assoc,
    IsPullback.isoPullback_hom_snd]

/-- Through `isoSpecTensor` and `X ≅ Spec Γ(X, ⊤)`, the morphism `g'` is `Spec` of the inclusion
`Γ(X, ⊤) → Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)`. -/
theorem isoSpecTensor_hom_fst :
    letI := affineSectionsAlgebra f
    letI := affineSectionsAlgebra g
    (isoSpecTensor hpb).hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : Γ(X, ⊤) →+* Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤))) =
      g' ≫ X.isoSpec.hom := by
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  simp only [isoSpecTensor, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [pullbackSpecIso_hom_fst, pullback.lift_fst, ← Category.assoc,
    IsPullback.isoPullback_hom_fst]

/-- The inverse of `isoSpecTensor` followed by `g'` is `Spec` of the inclusion
`Γ(X, ⊤) → Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)` followed by `Spec Γ(X, ⊤) ≅ X`. -/
theorem isoSpecTensor_inv_comp :
    letI := affineSectionsAlgebra f
    letI := affineSectionsAlgebra g
    (isoSpecTensor hpb).inv ≫ g' = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : Γ(X, ⊤) →+* Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤))) ≫
      X.isoSpec.inv := by
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  rw [Iso.inv_comp_eq, ← Category.assoc, isoSpecTensor_hom_fst, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-! ### The diagonal opens `Spec(A ⊗_R A)` and `Spec(A' ⊗_{R'} A')` -/

namespace DiagonalOpen

variable (f) in
/-- The diagonal open `Spec(A ⊗_R A)` of `f`, for `X`, `S` affine. -/
abbrev affineSpec : DiagonalOpen f :=
  let := affineSectionsAlgebra f
  ofSpec f X.isoSpec S.isoSpec (isoSpec_hom_specMap_algebraMap f)

/-- The diagonal open `Spec(A' ⊗_{R'} A')` of `f'`, for the base change of affine schemes. -/
abbrev affineSpecBaseChange : DiagonalOpen f' :=
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  ofSpec f' (isoSpecTensor hpb) S'.isoSpec (isoSpecTensor_hom_snd hpb)

/-- `Spec(A' ⊗_{R'} A') ⟶ Spec(A ⊗_R A)`, induced by `A ⊗_R A ⟶ A' ⊗_{R'} A'`. -/
abbrev affineSpecBaseChangeHom :
    (affineSpecBaseChange hpb).W ⟶ (affineSpec f).W :=
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  Spec.map (envelopingBaseChangeHom Γ(S, ⊤) Γ(X, ⊤) Γ(S', ⊤))

omit [IsAffine X] [IsAffine S] [IsAffine S'] in
/-- On the left factor of `A ⊗_R A`, the map `A ⊗_R A → A' ⊗_{R'} A'` with `A' = A ⊗_R R'` is the
inclusion `A → A'` followed by the left factor of `A' ⊗_{R'} A'`. -/
theorem envelopingLeft_comp_envelopingBaseChangeHom (R A R' : CommRingCat.{u}) [Algebra R A]
    [Algebra R R'] :
    envelopingLeft R A ≫ envelopingBaseChangeHom R A R' =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R') ≫
        envelopingLeft R' (CommRingCat.of (A ⊗[R] R')) := by
  ext a
  simp [Dualizing.envelopingBaseChangeRingHom]
  rfl

omit [IsAffine X] [IsAffine S] [IsAffine S'] in
/-- On the right factor of `A ⊗_R A`, the map `A ⊗_R A → A' ⊗_{R'} A'` with `A' = A ⊗_R R'` is the
inclusion `A → A'` followed by the right factor of `A' ⊗_{R'} A'`. -/
theorem envelopingRight_comp_envelopingBaseChangeHom (R A R' : CommRingCat.{u}) [Algebra R A]
    [Algebra R R'] :
    envelopingRight R A ≫ envelopingBaseChangeHom R A R' =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R') ≫
        envelopingRight R' (CommRingCat.of (A ⊗[R] R')) := by
  ext a
  simp [Dualizing.envelopingBaseChangeRingHom]
  rfl

/-- `Spec(A' ⊗_{R'} A') ⟶ Spec(A ⊗_R A)` is the restriction of `g' × g'`. -/
theorem affineSpecBaseChangeHom_ι :
    affineSpecBaseChangeHom hpb ≫ (affineSpec f).ι =
      (affineSpecBaseChange hpb).ι ≫ pullbackMapOfIsPullback hpb := by
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  dsimp only [affineSpec, affineSpecBaseChange, affineSpecBaseChangeHom, ofSpec]
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullbackMapOfIsPullback_fst, pullbackMapOfIsPullback_snd,
      ofSpecι_fst, ofSpecι_snd, ofSpecι_fst_assoc, ofSpecι_snd_assoc, isoSpecTensor_inv_comp,
      ← Spec.map_comp_assoc, envelopingLeft_comp_envelopingBaseChangeHom,
      envelopingRight_comp_envelopingBaseChangeHom]

/-! ### Base change of the generator -/

/-- Generators are unchanged by applying a functor to a conjugate. -/
theorem _root_.Dualizing.IsPostcompGenerator.map_conj_iff {C E : Type*} [Category* C]
    [Category* E] (F : C ⥤ E) {X X' Y Y' : C} (a : X' ≅ X) (b : Y ≅ Y') (x : X ⟶ Y) :
    Dualizing.IsPostcompGenerator (F.map (a.hom ≫ x ≫ b.hom)) ↔
      Dualizing.IsPostcompGenerator (F.map x) := by
  rw [F.map_comp, F.map_comp]
  exact Dualizing.IsPostcompGenerator.conj_iff (F.mapIso a).symm (F.mapIso b) (F.map x)

/-- Generators are unchanged by applying a functor to a conjugate. -/
theorem _root_.Dualizing.IsPostcompGenerator.map_conj_inv_iff {C E : Type*} [Category* C]
    [Category* E] (F : C ⥤ E) {X X' Y Y' : C} (a : X ≅ X') (b : Y ≅ Y') (x : X ⟶ Y) :
    Dualizing.IsPostcompGenerator (F.map (a.inv ≫ x ≫ b.hom)) ↔
      Dualizing.IsPostcompGenerator (F.map x) :=
  Dualizing.IsPostcompGenerator.map_conj_iff F a.symm b x

omit [IsAffine X] [IsAffine S] [IsAffine S'] in
/-- The open immersion of a diagonal open into a diagonal open which is all of `X ×_S X`. -/
theorem diag_comp_ι_inv {D₀ : DiagonalOpen f} (D : DiagonalOpen f) [IsIso D₀.ι] :
    D.diag ≫ D.ι ≫ inv D₀.ι = D₀.diag := by
  rw [← Category.assoc, D.fac, ← D₀.fac, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- `L(g')^*K` read on `Spec(A ⊗_R R')` is the sheaf associated to `RΓ(X, K) ⊗ᴸ_A (A ⊗_R R')`. -/
def derivedPullbackIsoSpecTensorIso (K : DerivedCategory X.Modules)
    (eK : (derivedPullback X.isoSpec.inv.toLRSHom.toShHom).obj K ≅
      (tilde.functor Γ(X, ⊤)).mapDerivedCategory.obj ((derivedSectionsUnbounded X ⊤).obj K)) :
    letI := affineSectionsAlgebra f
    letI := affineSectionsAlgebra g
    (derivedPullback (isoSpecTensor hpb).inv.toLRSHom.toShHom).obj (baseChangeComplex g' K) ≅
      (tilde.functor (CommRingCat.of (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)))).mapDerivedCategory.obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom :
            Γ(X, ⊤) →+* Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤))).functor.obj
          ((derivedSectionsUnbounded X ⊤).obj K)) :=
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  Scheme.derivedPullbackCompObj (isoSpecTensor hpb).inv g' K ≪≫
    Scheme.derivedPullbackCongrObj (isoSpecTensor_inv_comp hpb) K ≪≫
    (Scheme.derivedPullbackCompObj (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : Γ(X, ⊤) →+* Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤))))
        X.isoSpec.inv K).symm ≪≫
    (derivedPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom :
        Γ(X, ⊤) →+* Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)))).toLRSHom.toShHom).mapIso eK ≪≫
    (StandardModel.affinePullbackComparison Γ(X, ⊤)
      (CommRingCat.of (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)))
      (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)).app
        ((derivedSectionsUnbounded X ⊤).obj K)

/-- **The "moreover" clause of Stacks 0E2F on the diagonal opens `Spec(A ⊗_R A)` and
`Spec(A' ⊗_{R'} A')`**, for the base change of affine schemes. -/
theorem isPostcompGenerator_affineSpecBaseChange [Flat f] [LocallyOfFinitePresentation f]
    (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hKA : letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
        moduleFlat_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
      letI : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
        algebraFinitePresentation_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
      Dualizing.IsRelativeDualizingComplex Γ(S, ⊤) Γ(X, ⊤) ((derivedSectionsUnbounded X ⊤).obj K))
    (ξS : (affineSpec f).diagonalObject ⟶ (affineSpec f).derivedPullbackProj K)
    (hξS : Dualizing.IsPostcompGenerator ξS) :
    Dualizing.IsPostcompGenerator
      ((baseChangeDiagonalIso hpb (affineSpec f) (affineSpecBaseChange hpb)
          (affineSpecBaseChangeHom hpb) (affineSpecBaseChangeHom_ι hpb)).inv ≫
        (derivedPullback (affineSpecBaseChangeHom hpb).toLRSHom.toShHom).map ξS ≫
        (derivedPullbackProjBaseChangeIso (affineSpec f) (affineSpecBaseChange hpb) g'
          (affineSpecBaseChangeHom hpb)
          (proj_baseChange hpb _ _ _ (affineSpecBaseChangeHom_ι hpb)) K).hom) := by
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  let : Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
    moduleFlat_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
  let : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
    algebraFinitePresentation_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
  obtain ⟨eK⟩ := nonempty_derivedPullback_isoSpec_inv_iso K hK
  exact ofSpec_isPostcompGenerator_baseChange f X.isoSpec S.isoSpec
    (isoSpec_hom_specMap_algebraMap f) f' (isoSpecTensor hpb) S'.isoSpec
    (isoSpecTensor_hom_snd hpb) K _ eK hKA (baseChangeComplex g' K)
    (derivedPullbackIsoSpecTensorIso hpb K eK) ξS hξS
    (baseChangeDiagonalIso hpb (affineSpec f) (affineSpecBaseChange hpb)
      (affineSpecBaseChangeHom hpb) (affineSpecBaseChangeHom_ι hpb)).symm
    (derivedPullbackProjBaseChangeIso (affineSpec f) (affineSpecBaseChange hpb) g'
      (affineSpecBaseChangeHom hpb) (proj_baseChange hpb _ _ _ (affineSpecBaseChangeHom_ι hpb)) K)

/-- **Base change of the generator, over affine schemes.** Let `f : X ⟶ S` be flat and locally of
finite presentation with `X`, `S`, `S'` affine, `K` an object of `D(𝒪_X)` with quasi-coherent
cohomology such that `RΓ(X, K)` is a relative dualizing complex for `Γ(S, ⊤) → Γ(X, ⊤)`, and
`ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` a generator. For a diagonal open `W'` of `f'` with `w : W' ⟶ W` the
restriction of `g' × g'`, and any identifications `φ`, `ψ`, the derived base change
`φ ≫ Lw^*ξ ≫ ψ : Δ'_*𝒪_{X'} ⟶ L pr₁^*(L(g')^*K)|_{W'}` is a generator. -/
theorem isPostcompGenerator_baseChange_of_isAffine [Flat f] [LocallyOfFinitePresentation f]
    (D : DiagonalOpen f) (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
    (hw : w ≫ D.ι = D'.ι ≫ pullbackMapOfIsPullback hpb) (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hKA : letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
        moduleFlat_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
      letI : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
        algebraFinitePresentation_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
      Dualizing.IsRelativeDualizingComplex Γ(S, ⊤) Γ(X, ⊤) ((derivedSectionsUnbounded X ⊤).obj K))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) (hξ : Dualizing.IsPostcompGenerator ξ)
    (φ : D'.diagonalObject ≅ (derivedPullback w.toLRSHom.toShHom).obj D.diagonalObject)
    (ψ : (derivedPullback w.toLRSHom.toShHom).obj (D.derivedPullbackProj K) ≅
      D'.derivedPullbackProj (baseChangeComplex g' K)) :
    Dualizing.IsPostcompGenerator
      (φ.hom ≫ (derivedPullback w.toLRSHom.toShHom).map ξ ≫ ψ.hom) := by
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  let DS := affineSpec f
  let DS' := affineSpecBaseChange hpb
  let wS := affineSpecBaseChangeHom hpb
  have hwS : wS ≫ DS.ι = DS'.ι ≫ pullbackMapOfIsPullback hpb := affineSpecBaseChangeHom_ι hpb
  have : IsIso DS.ι := inferInstanceAs
    (IsIso (ofSpecι f X.isoSpec S.isoSpec (isoSpec_hom_specMap_algebraMap f)))
  have : IsIso DS'.ι := inferInstanceAs
    (IsIso (ofSpecι f' (isoSpecTensor hpb) S'.isoSpec (isoSpecTensor_hom_snd hpb)))
  have := D.isOpenImmersion
  have := D'.isOpenImmersion
  -- extension of `ξ` from `W` to `Spec(A ⊗_R A)`
  let j : D.W ⟶ DS.W := D.ι ≫ inv DS.ι
  have hj : D.diag ≫ j = DS.diag := diag_comp_ι_inv D
  have hjι : j ≫ DS.ι = D.ι := by simp [j]
  have hw₀ : j ≫ DS.ι = D.ι ≫ pullbackMapOfIsPullback (IsPullback.id_horiz f) := by
    rw [hjι, pullbackMapOfIsPullback, pullback.map_id, Category.comp_id]
  let θ₁ : (derivedPullback j.toLRSHom.toShHom).obj DS.diagonalObject ≅ D.diagonalObject :=
    baseChangeDiagonalIso (IsPullback.id_horiz f) DS D j hw₀
  have hjp : j ≫ DS.proj = D.proj := by
    simp only [proj, ← Category.assoc, hjι]
  let θ₂ : (derivedPullback j.toLRSHom.toShHom).obj (DS.derivedPullbackProj K) ≅
      D.derivedPullbackProj K :=
    Scheme.derivedPullbackCompObj _ _ K ≪≫ Scheme.derivedPullbackCongrObj hjp K
  obtain ⟨ξS, hξS⟩ := D.exists_derivedPullback_eq DS j hj θ₁ θ₂ ξ
  have hgenS : Dualizing.IsPostcompGenerator ξS := by
    refine (D.isPostcompGenerator_derivedPullback_iff DS j hj ξS).1 ?_
    rw [hξS]
    exact (Dualizing.IsPostcompGenerator.conj_iff θ₁.symm θ₂.symm ξ).2 hξ
  -- restriction to `W'`
  let j' : D'.W ⟶ DS'.W := D'.ι ≫ inv DS'.ι
  have hgen := (Dualizing.IsPostcompGenerator.map_conj_inv_iff
    (derivedPullback j'.toLRSHom.toShHom) _ _ _).1
      ((D'.isPostcompGenerator_derivedPullback_iff DS' j' (diag_comp_ι_inv D') _).2
        (isPostcompGenerator_affineSpecBaseChange hpb K hK hKA ξS hgenS))
  have hcomm : j' ≫ wS = w ≫ j := by
    rw [← cancel_mono DS.ι, Category.assoc, hwS, Category.assoc w, hjι, hw]
    simp [j']
  have hsh : j'.toLRSHom.toShHom ≫ wS.toLRSHom.toShHom =
      w.toLRSHom.toShHom ≫ j.toLRSHom.toShHom := by
    rw [← LocallyRingedSpace.comp_toShHom, ← Scheme.Hom.comp_toLRSHom, hcomm,
      Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom]
  let α : derivedPullback wS.toLRSHom.toShHom ⋙ derivedPullback j'.toLRSHom.toShHom ≅
      derivedPullback j.toLRSHom.toShHom ⋙ derivedPullback w.toLRSHom.toShHom :=
    Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical _ _ ≪≫
      eqToIso (by rw [hsh]) ≪≫
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical _ _).symm
  have h : Dualizing.IsPostcompGenerator ((derivedPullback w.toLRSHom.toShHom).map
      ((derivedPullback j.toLRSHom.toShHom).map ξS)) :=
    Dualizing.IsPostcompGenerator.map_natIso (f := ξS) α hgen
  rw [hξS] at h
  exact (Dualizing.IsPostcompGenerator.conj_iff φ.symm ψ _).2
    ((Dualizing.IsPostcompGenerator.map_conj_iff (derivedPullback w.toLRSHom.toShHom) θ₁ θ₂.symm
      ξ).1 h)

end DiagonalOpen

end AlgebraicGeometry.Scheme.Hom

end
