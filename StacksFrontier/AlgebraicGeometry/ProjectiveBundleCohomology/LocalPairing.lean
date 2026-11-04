module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.SymPieceBasis
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TwistPairing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.GradedIsoPairing
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.AffineSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Cohomology.SchemeOpenRestriction.Basic
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Pointwise
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.IsoOnBasis
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.LocalModel

/-!
# The multiplication pairing over a trivializing affine open

Let `π : 𝐏(E) ⟶ S` be the projective bundle of a finite locally free `𝒪_S`-module `E` of rank
`n + 1`, `d ≤ -n - 2` and `k = -n - 1 - d`. Over an affine open `V ⊆ S` on which `E` is free, the
cohomology over `π⁻¹(V)` of the curried multiplication pairing

`𝒪(d) ⟶ SheafHom(π^* Sym^k(E), 𝒪(-n-1))`

is an isomorphism in degree `n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

/-- **Linear maps out of an extension of scalars of a free module are determined freely by
their values on the images of a basis.** -/
theorem bijective_apply_extendScalars_basis {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {M : ModuleCat.{u} R} {N P : ModuleCat.{u} S}
    (e : (ModuleCat.extendScalars f).obj M ≅ N) {ι : Type*} (b : Module.Basis ι R M) :
    Function.Bijective
      (fun g : N →ₗ[S] P => fun i => g (e.hom ((1 : S) ⊗ₜ[R, f] b i))) :=
  (ModuleCat.homEquiv.symm.trans ((e.symm.homCongr (Iso.refl P)).trans
    (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).trans
      (ModuleCat.homEquiv.trans (b.constr ℕ).symm.toEquiv)))).bijective

/-- **A map whose composite with an isomorphism onto a finite direct sum is bijective
componentwise is sent to a bijection** by an additive functor to abelian groups. -/
theorem bijective_map_of_isIso_biproductLift {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {J : Type}
    [Finite J] (L : J → 𝒞) [HasBiproduct L] (H : 𝒞 ⥤ AddCommGrpCat.{u}) [H.Additive]
    {M N : 𝒞} (φ : M ⟶ N) (ev : N ⟶ ⨁ L) (hev : IsIso ev)
    (h : Function.Bijective (fun c => fun i => (H.map (φ ≫ ev ≫ biproduct.π L i)).hom c)) :
    Function.Bijective (H.map φ).hom := by
  have := Fintype.ofFinite J
  refine (Function.Bijective.of_comp_iff' ((ProjectiveSpacePairing.bijective_biproduct_components
    L H).comp (ConcreteCategory.bijective_of_isIso (H.map ev))) _).1 ?_
  have heq : ((fun y => fun s => (H.map (biproduct.π L s)).hom y) ∘ (H.map ev).hom) ∘
      (H.map φ).hom = fun c => fun i => (H.map (φ ≫ ev ≫ biproduct.π L i)).hom c :=
    funext fun c => funext fun i => by
      simp only [Function.comp_apply, Functor.map_comp, AddCommGrpCat.hom_comp,
        AddMonoidHom.comp_apply]
  exact heq ▸ h

section ImageTop

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

/-- **Cohomology over the image of an open immersion, naturally in the module**:
`Hᵠ(j(X), -) ≅ Hᵠ(X, j^* -)`. -/
def hfunctorImageTopIso (q : ℕ) :
    Hfunctor Y.ringCatSheaf (j ''ᵁ ⊤) q ≅
      Scheme.Modules.restrictFunctor j ⋙ Hfunctor X.ringCatSheaf ⊤ q :=
  eqToIso (by rw [j.image_top_eq_opensRange]) ≪≫
    Stacks.Cohomology.SchemeOpenRestriction.hfunctorRestrictNatIso Y j.opensRange q ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor j.opensRange.ι)
      (Stacks.Cohomology.ModuleComparison.hfunctorPullbackIso j.isoOpensRange q).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor j.opensRange.ι)
          (Scheme.Modules.restrictFunctorIsoPullback j.isoOpensRange.hom).symm ≪≫
        (Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).symm ≪≫
        Scheme.Modules.restrictFunctorCongr j.isoOpensRange_hom_ι) _

/-- A morphism `φ` of modules on `Y` induces an isomorphism on `Hᵠ(j(X), -)` if and only if
`j^* φ` induces an isomorphism on `Hᵠ(X, -)`. -/
theorem isIso_hfunctor_image_top_map_iff (q : ℕ) {F G : Y.Modules} (φ : F ⟶ G) :
    IsIso ((Hfunctor Y.ringCatSheaf (j ''ᵁ ⊤) q).map φ) ↔
      IsIso ((Hfunctor X.ringCatSheaf ⊤ q).map ((Scheme.Modules.restrictFunctor j).map φ)) :=
  NatIso.isIso_map_iff (hfunctorImageTopIso j q) φ

end ImageTop

section Evaluation

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {X C : Scheme.{u}} (j : C ⟶ X) [IsOpenImmersion j] (A L : X.Modules)

/-- The restriction of a section over the image of `j` to the image of an open of the source. -/
abbrev resImage (t : A.val.obj (op (j ''ᵁ ⊤))) (W : C.Opens) : A.val.obj (op (j ''ᵁ W)) :=
  A.val.map (homOfLE (j.image_mono le_top)).op t

/-- Evaluation at a section, on the sections over one open of the source of `j`. -/
def sheafHomEvalLinear (t : A.val.obj (op (j ''ᵁ ⊤))) (W : C.Opens) :
    (((Stacks.Algebraization.sheafHomFunctor X A).obj L).restrict j).val.obj (op W) →ₗ[
      C.ringCatSheaf.obj.obj (op W)] (L.restrict j).val.obj (op W) where
  toFun f := Stacks.Algebraization.internalHomEvaluation A L (j ''ᵁ W) f (resImage j A t W)
  map_add' f g := rfl
  map_smul' r f := LinearMap.congr_fun
    ((Stacks.Algebraization.internalHomEvaluation A L (j ''ᵁ W)).map_smul
      ((j.appIso W).inv r) f) (resImage j A t W)

/-- Evaluation at the section `t` commutes with restriction from `W` to an open `W' ≤ W`. -/
theorem sheafHomEvalLinear_naturality (t : A.val.obj (op (j ''ᵁ ⊤))) {W W' : C.Opens}
    (hW : W' ≤ W)
    (f : ((Stacks.Algebraization.sheafHomFunctor X A).obj L).val.obj (op (j ''ᵁ W))) :
    sheafHomEvalLinear j A L t W'
        ((((Stacks.Algebraization.sheafHomFunctor X A).obj L).restrict j).val.map
          (homOfLE hW).op f) =
      (L.restrict j).val.map (homOfLE hW).op (sheafHomEvalLinear j A L t W f) := by
  let i : (Over.mk (homOfLE (j.image_mono hW)) : Over (j ''ᵁ W)) ⟶ Over.mk (𝟙 (j ''ᵁ W)) :=
    Over.homMk (homOfLE (j.image_mono hW)) (Subsingleton.elim _ _)
  have hres : resImage j A t W' = A.val.map (homOfLE (j.image_mono hW)).op (resImage j A t W) :=
    PresheafOfModules.map_comp_apply A.val (homOfLE (j.image_mono le_top)).op
      (homOfLE (j.image_mono hW)).op t
  show (f.app (op (Over.mk (homOfLE (j.image_mono hW))))).hom (resImage j A t W') =
    L.val.map (homOfLE (j.image_mono hW)).op ((f.app (op (Over.mk (𝟙 (j ''ᵁ W))))).hom
      (resImage j A t W))
  rw [hres]
  exact ConcreteCategory.congr_hom (f.naturality i.op) (resImage j A t W)

/-- **Evaluation at a section**: a section `t` of `A` over the image of the open immersion `j`
gives `j^* SheafHom(A, L) ⟶ j^* L`, `f ↦ f(t)`. -/
def sheafHomEval (t : A.val.obj (op (j ''ᵁ ⊤))) :
    ((Stacks.Algebraization.sheafHomFunctor X A).obj L).restrict j ⟶ L.restrict j where
  val :=
    { app W := ModuleCat.homEquiv.symm (sheafHomEvalLinear j A L t W.unop)
      naturality {W W'} g := by
        ext f
        exact sheafHomEvalLinear_naturality j A L t (leOfHom g.unop) f }

/-- On an open `W` of the source of `j`, `sheafHomEval j A L t` sends `f` to its value at the
restriction of `t` to `j(W)`. -/
theorem sheafHomEval_app (t : A.val.obj (op (j ''ᵁ ⊤))) (W : C.Opens)
    (f : ((Stacks.Algebraization.sheafHomFunctor X A).obj L).val.obj (op (j ''ᵁ W))) :
    (sheafHomEval j A L t).val.app (op W) f =
      Stacks.Algebraization.internalHomEvaluation A L (j ''ᵁ W) f (resImage j A t W) :=
  rfl

/-- **Evaluation at the images of a basis is bijective over an affine open.** If the sections
of the quasi-coherent module `A` over the affine open `j(W)` are the extension of scalars of a
free module, with the images of a basis given by sections `t i`, then `f ↦ (f(t i))_i` is a
bijection from the sections of `SheafHom(A, L)` over `j(W)`. -/
theorem bijective_sheafHomEval {ι : Type*} (t : ι → A.val.obj (op (j ''ᵁ ⊤))) (W : C.Opens)
    (hW : IsAffineOpen (j ''ᵁ W)) [A.IsQuasicoherent] {R : Type u} [CommRing R]
    (f : R →+* Γ(X, j ''ᵁ W)) {M : ModuleCat.{u} R}
    (e : (ModuleCat.extendScalars f).obj M ≅ ModuleCat.of Γ(X, j ''ᵁ W) Γ(A, j ''ᵁ W))
    (b : Module.Basis ι R M)
    (hb : ∀ i, e.hom ((1 : Γ(X, j ''ᵁ W)) ⊗ₜ[R, f] b i) = resImage j A (t i) W) :
    Function.Bijective
      (fun x => fun i => (sheafHomEval j A L (t i)).val.app (op W) x) := by
  have heq : (fun x => fun i => (sheafHomEval j A L (t i)).val.app (op W) x) =
      (fun g : Γ(A, j ''ᵁ W) →ₗ[Γ(X, j ''ᵁ W)] Γ(L, j ''ᵁ W) =>
        fun i => g (e.hom ((1 : Γ(X, j ''ᵁ W)) ⊗ₜ[R, f] b i))) ∘
        Stacks.Algebraization.internalHomEvaluation A L (j ''ᵁ W) :=
    funext fun x => funext fun i => by
      show Stacks.Algebraization.internalHomEvaluation A L (j ''ᵁ W) x (resImage j A (t i) W) =
        Stacks.Algebraization.internalHomEvaluation A L (j ''ᵁ W) x
          (e.hom ((1 : Γ(X, j ''ᵁ W)) ⊗ₜ[R, f] b i))
      rw [hb]
  rw [heq]
  exact (bijective_apply_extendScalars_basis f e (P := ModuleCat.of Γ(X, j ''ᵁ W) Γ(L, j ''ᵁ W))
    b).comp (Stacks.Algebraization.internalHomEvaluation_bijective A L ⟨j ''ᵁ W, hW⟩)

/-- **Evaluation at the pullbacks of a basis is bijective over an affine open.** For a
quasi-coherent `G` on `Y`, an affine open `U` of `Y` over which `Γ(G, U)` has a basis `b`, and an
affine open `j(W)` mapping into `U` under `f`, evaluation of the sections of
`SheafHom(f^* G, L)` over `j(W)` at the pullbacks of the `b i` is a bijection. -/
theorem bijective_sheafHomEval_pullback {Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules)
    [G.IsQuasicoherent] {U : Y.Opens} (hU : IsAffineOpen U) {ι : Type*}
    (b : Module.Basis ι Γ(Y, U) Γ(G, U))
    (t : ι → ((Scheme.Modules.pullback f).obj G).val.obj (op (j ''ᵁ ⊤))) (W : C.Opens)
    (hW : IsAffineOpen (j ''ᵁ W)) (hle : j ''ᵁ W ≤ f ⁻¹ᵁ U)
    (ht : ∀ i, resImage j _ (t i) W = Scheme.Modules.pullbackSection f G U _ hle (b i)) :
    Function.Bijective (fun x => fun i =>
      (sheafHomEval j ((Scheme.Modules.pullback f).obj G) L (t i)).val.app (op W) x) :=
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback f G
  bijective_sheafHomEval j _ L t W hW (f.appLE U (j ''ᵁ W) hle).hom
    (AlgebraicGeometry.affinePullbackSectionsBaseChangeIso f G hU hW hle) b fun i =>
      (AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul f G hU hW hle (b i)).trans
        (ht i).symm

/-- **Evaluation at a family of sections is an isomorphism onto a finite direct sum** as soon as
it is bijective on the sections over every affine open. -/
theorem isIso_biproductLift_sheafHomEval {ι : Type} [Finite ι] (t : ι → A.val.obj (op (j ''ᵁ ⊤)))
    (h : ∀ W : C.Opens, IsAffineOpen W →
      Function.Bijective (fun x => fun i => (sheafHomEval j A L (t i)).val.app (op W) x)) :
    IsIso (biproduct.lift (fun i => sheafHomEval j A L (t i)) :
      ((Stacks.Algebraization.sheafHomFunctor X A).obj L).restrict j ⟶
        ⨁ (fun _ : ι => L.restrict j)) := by
  have := Fintype.ofFinite ι
  refine isIso_of_bijective_app_basis _ C.isBasis_affineOpens fun W hW => ?_
  let H : C.Modules ⥤ AddCommGrpCat.{u} := secF C.ringCatSheaf W
  have : H.Additive := secFAdditive C.ringCatSheaf W
  exact bijective_map_of_isIso_biproductLift (fun _ : ι => L.restrict j) H _ (𝟙 _) inferInstance
    (by simp only [Category.id_comp, biproduct.lift_π]; exact h W hW)

end Evaluation

section Absolute

open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjTwists

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {R : Type u} {σ : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- In the localization of `R` at `p`, right multiplication by `a / 1` is the localization of
left multiplication by `a`. -/
theorem mul_mk_eq_map_mulLeft {p : Submonoid R} (a : R) (z : LocalizedModule p R) :
    z * LocalizedModule.mk a 1 = LocalizedModule.map p (LinearMap.mulLeft R a) z := by
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.map_mk]
    show Localization.mk m s * Localization.mk a (1 : p) = Localization.mk (a * m) s
    rw [Localization.mk_mul]
    exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [mul_comm]))

/-- **The product with a homogeneous element of degree `k`, read as a section of `𝒪(k)`, is
multiplication by that element.** -/
theorem eqToHom_absoluteTwistProduct_degreeSection {k : ℕ} (a : 𝒮 k) (d e : ℤ)
    (he : (k : ℤ) + d = e) (hde : d + k = e) (W : (AlgebraicGeometry.Proj 𝒮).Opens)
    (c : (twistingSheaf 𝒮 d).val.obj (op W)) :
    (eqToHom (congrArg (twistingSheaf 𝒮) hde)).val.app (op W)
        (absoluteTwistProduct 𝒮 d k W c
          ((twistingSheaf 𝒮 k).val.map (homOfLE le_top).op
            (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 k a))) =
      (twistMulLeftIntOf 𝒮 a d e he).val.app (op W) c := by
  subst hde
  apply Subtype.ext
  funext x
  refine (Stacks.AlgebraicGeometry.TwistRigidity.absoluteTwistProduct_apply 𝒮 d k W c _ x).trans
    ((congrArg (c.1 x * ·) (ProjTwistSections.degreeSection_apply 𝒮 k a ⟨x.1, trivial⟩)).trans ?_)
  exact mul_mk_eq_map_mulLeft (a : R) (c.1 x)

end Absolute

section PullbackSection

/-- The adjoint `f^* G ⟶ M` of a map `ψ : G ⟶ f_* M` sends the pullback of a section `s` to the
restriction of `ψ(s)`. -/
theorem homEquiv_symm_pullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules)
    (M : X.Modules) (ψ : G ⟶ (Scheme.Modules.pushforward f).obj M) (V : Y.Opens) (U : X.Opens)
    (h : U ≤ f ⁻¹ᵁ V) (s : G.val.obj (op V)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm ψ).val.app (op U)
        (Scheme.Modules.pullbackSection f G V U h s) =
      M.val.map (homOfLE h).op (ψ.val.app (op V) s) := by
  have h1 : ψ = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G ≫
      (Scheme.Modules.pushforward f).map
        (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm ψ) :=
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)).symm
  refine (PresheafOfModules.naturality_apply
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm ψ).val
    (homOfLE h).op _).trans ?_
  refine congrArg (ConcreteCategory.hom (M.val.map (homOfLE h).op)) ?_
  conv_rhs => rw [h1]
  rfl

/-- Restricting the pullback of a section is pulling back to the smaller open. -/
theorem map_pullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) (V : Y.Opens)
    {U U' : X.Opens} (h : U ≤ f ⁻¹ᵁ V) (hU : U' ≤ U) (s : G.val.obj (op V)) :
    ((Scheme.Modules.pullback f).obj G).val.map (homOfLE hU).op
        (Scheme.Modules.pullbackSection f G V U h s) =
      Scheme.Modules.pullbackSection f G V U' (hU.trans h) s :=
  (PresheafOfModules.map_comp_apply _ _ _ _).symm

end PullbackSection

section Chart

open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjTwists Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (D : TwistData A) {V : S.Opens}
  (hV : IsAffineOpen V)

/-- The chart comparison of sections commutes with restriction. -/
theorem map_mapSection (n : ℤ) {W W' : (AlgebraicGeometry.Proj (A.grading V)).Opens}
    (h : W ≤ W') (a : (twistingSheaf (A.grading V) n).val.obj (op W')) :
    letI := D.chartData.chart_isOpenImmersion V hV
    (D.algebra.piece n).val.map (homOfLE (((relativeProj A).chart V hV).image_mono h)).op
        (D.chartData.mapSection V hV n W' a) =
      D.chartData.mapSection V hV n W ((twistingSheaf (A.grading V) n).val.map (homOfLE h).op a) :=
  let := D.chartData.chart_isOpenImmersion V hV
  (PresheafOfModules.naturality_apply (D.chartData.chartIso V hV n).inv.val (homOfLE h).op a).symm

/-- The chart comparison of sections commutes with the identifications of equal degrees. -/
theorem eqToHom_mapSection {n n' : ℤ} (hn : n = n')
    (W : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (a : (twistingSheaf (A.grading V) n).val.obj (op W)) :
    letI := D.chartData.chart_isOpenImmersion V hV
    (eqToHom (congrArg D.algebra.piece hn)).val.app (op (((relativeProj A).chart V hV) ''ᵁ W))
        (D.chartData.mapSection V hV n W a) =
      D.chartData.mapSection V hV n' W
        ((eqToHom (congrArg (twistingSheaf (A.grading V)) hn)).val.app (op W) a) := by
  subst hn
  rfl

/-- Restricting a section over `b` to `U` agrees with restricting its transport along `b = a`
to `U`. -/
theorem transport_map {X : Scheme.{u}} (𝒢 : SchemeGradedAlgebra X) (n : ℤ) {a b : X.Opens}
    (hab : b = a) (x : (𝒢.piece n).val.obj (op b)) {U : X.Opens} (h1 : U ≤ a) (h2 : U ≤ b) :
    (𝒢.piece n).val.map (homOfLE h2).op x = (𝒢.piece n).val.map (homOfLE h1).op (hab ▸ x) := by
  subst hab
  rfl

/-- **The homogeneous sections over the chart**: the restriction of `ψ_k(s)` to the image of an
open of the chart is the restriction of the section of `𝒪(k)` given by `s`. -/
theorem map_psi_eq_mapSection (k : ℕ) (W : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (s : A.sectionPieces V k)
    (hW : (letI := D.chartData.chart_isOpenImmersion V hV; ((relativeProj A).chart V hV) ''ᵁ W) ≤
      (relativeProj A).toBase ⁻¹ᵁ V) :
    letI := D.chartData.chart_isOpenImmersion V hV
    (D.algebra.piece (k : ℤ)).val.map (homOfLE hW).op ((D.ψ k).val.app (op V) s) =
      D.chartData.mapSection V hV (k : ℤ) W
        ((twistingSheaf (A.grading V) (k : ℤ)).val.map (homOfLE le_top).op
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading V) k
            ⟨DirectSum.of (A.sectionPieces V) k s, A.of_mem_grading V s⟩)) := by
  let := D.chartData.chart_isOpenImmersion V hV
  refine (transport_map D.algebra (k : ℤ) (D.chartData.chart_range V hV).symm _
    (((relativeProj A).chart V hV).image_mono le_top) hW).trans ?_
  refine (congrArg (ConcreteCategory.hom ((D.algebra.piece (k : ℤ)).val.map
    (homOfLE (((relativeProj A).chart V hV).image_mono le_top)).op))
      (D.ψ_chart V hV k s)).symm.trans ?_
  exact map_mapSection D hV (k : ℤ) le_top _

end Chart

section Bundle

open ProjectiveSpacePairing
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjTwists Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)) {V : S.Opens}
  (hV : IsAffineOpen V)

/-- The pullback of a section of `Sym^k(E)` over `V` to the image of the chart over `V`. -/
def chartPullbackSection (k : ℕ)
    (s : Γ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ), V)) :
    letI := D.chartData.chart_isOpenImmersion V hV
    ((Scheme.Modules.pullback
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))).val.obj
      (op (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) ''ᵁ ⊤)) :=
  Scheme.Modules.pullbackSection _ _ V _ (D.chartData.chart_range V hV).le s

/-- The adjoint `psiFlat E hqc D k` of `ψ_k` sends the restriction of
`chartPullbackSection E hqc D hV k s` to the image of `W` to the chart comparison of the section
of `𝒪(k)` given by `s`. -/
theorem psiFlat_chartPullbackSection (k : ℕ)
    (s : Γ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ), V))
    (W : (AlgebraicGeometry.Proj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)).Opens) :
    letI := D.chartData.chart_isOpenImmersion V hV
    (psiFlat E hqc D k).val.app
      (op (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) ''ᵁ W))
      (resImage _ _ (chartPullbackSection E hqc D hV k s) W) =
      D.chartData.mapSection V hV (k : ℤ) W
        ((twistingSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)
          (k : ℤ)).val.map (homOfLE le_top).op
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
            ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) k
            ⟨DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces V) k s,
              (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).of_mem_grading V s⟩)) :=
  let := D.chartData.chart_isOpenImmersion V hV
  have hle : ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) ''ᵁ W ≤
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V :=
    (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV).image_mono
      le_top).trans (D.chartData.chart_range V hV).le
  (congrArg (ConcreteCategory.hom ((psiFlat E hqc D k).val.app
      (op (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) ''ᵁ W))))
    (map_pullbackSection _ _ V (D.chartData.chart_range V hV).le
      (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV).image_mono
        le_top) s)).trans
    ((homEquiv_symm_pullbackSection _ _ _ (D.ψ k) V _ hle s).trans
      (map_psi_eq_mapSection D hV k W s hle))

/-- The restriction of `chartPullbackSection E hqc D hV k s` to the image of `W` under the chart
is the pullback of `s` to that open. -/
theorem resImage_chartPullbackSection (k : ℕ)
    (s : Γ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ), V))
    (W : (AlgebraicGeometry.Proj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)).Opens)
    (hle : (letI := D.chartData.chart_isOpenImmersion V hV
      ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) ''ᵁ W) ≤
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V) :
    letI := D.chartData.chart_isOpenImmersion V hV
    resImage _ _ (chartPullbackSection E hqc D hV k s) W =
      Scheme.Modules.pullbackSection _ _ V _ hle s :=
  let := D.chartData.chart_isOpenImmersion V hV
  map_pullbackSection _ _ V (D.chartData.chart_range V hV).le
    (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV).image_mono
      le_top) s

/-- **The pairing over the chart.** Evaluated at the pullback of a section `s` of `Sym^k(E)`,
the curried multiplication pairing is, on the chart over `V`, multiplication by `s`. -/
theorem sheafHomEval_twistPairingCurry (k : ℕ) (d e : ℤ) (he : d + k = e)
    (he' : (k : ℤ) + d = e)
    (s : Γ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ), V))
    (W : (AlgebraicGeometry.Proj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)).Opens)
    (c : (twistingSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) d).val.obj
      (op W)) :
    letI := D.chartData.chart_isOpenImmersion V hV
    (sheafHomEval ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV)
        ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))
        (D.algebra.piece e) (chartPullbackSection E hqc D hV k s)).val.app (op W)
        ((twistPairingCurry E hqc D k d e he).val.app
          (op (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) ''ᵁ W))
          (D.chartData.mapSection V hV d W c)) =
      D.chartData.mapSection V hV e W
        ((twistMulLeftIntOf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)
          ⟨DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces V) k s,
            (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).of_mem_grading V s⟩
          d e he').val.app (op W) c) :=
  let := D.chartData.chart_isOpenImmersion V hV
  (twistPairingCurry_apply E hqc D k d e he _ _ _).trans
    ((congrArg (fun z => (eqToHom (congrArg D.algebra.piece he)).val.app
        (op (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) ''ᵁ W))
        ((D.algebra.mul d (k : ℤ)).app
          (op (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) ''ᵁ W))
          (D.chartData.mapSection V hV d W c) z))
      (psiFlat_chartPullbackSection E hqc D hV k s W)).trans
    ((congrArg (fun z => (eqToHom (congrArg D.algebra.piece he)).val.app
        (op (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) ''ᵁ W))
        z)
      (D.chartIso_mul V hV d (k : ℤ) W c _).symm).trans
    ((eqToHom_mapSection D hV he W _).trans
      (congrArg (D.chartData.mapSection V hV e W)
        (eqToHom_absoluteTwistProduct_degreeSection _ _ d e he' he W c)))))

/-- **The pairing over the chart, as morphisms**: on the chart over `V`, the curried pairing
followed by evaluation at the pullback of `s` is multiplication by `s`. -/
theorem restrict_twistPairingCurry_sheafHomEval (k : ℕ) (d e : ℤ) (he : d + k = e)
    (he' : (k : ℤ) + d = e)
    (s : Γ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ), V)) :
    letI := D.chartData.chart_isOpenImmersion V hV
    (Scheme.Modules.restrictFunctor
        ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV)).map
        (twistPairingCurry E hqc D k d e he) ≫
      sheafHomEval ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV)
        ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))
        (D.algebra.piece e) (chartPullbackSection E hqc D hV k s) =
      (D.chartData.chartIso V hV d).hom ≫
        twistMulLeftIntOf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)
          ⟨DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces V) k s,
            (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).of_mem_grading V s⟩ d e he' ≫
        (D.chartData.chartIso V hV e).inv := by
  let := D.chartData.chart_isOpenImmersion V hV
  exact (Iso.inv_comp_eq _).mp (SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
    ModuleCat.hom_ext (LinearMap.ext fun c =>
      sheafHomEval_twistPairingCurry E hqc D hV k d e he he' s W.unop c)))

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

include hV in
/-- **Over a trivializing affine open, the curried pairing is an isomorphism on the top
cohomology over the preimage.** For `E` with a basis of `Γ(E, V)` of cardinality `m + 2`,
`k + d = -(m+1) - 1` and `e = -(m+1) - 1`,
`Hᵐ⁺¹(π⁻¹(V), 𝒪(d)) ⟶ Hᵐ⁺¹(π⁻¹(V), SheafHom(π^* Sym^k(E), 𝒪(e)))` is an isomorphism. -/
theorem isIso_hfunctor_preimage_twistPairingCurry {m : ℕ}
    (b : Module.Basis (Fin (m + 1 + 1)) Γ(S, V) Γ(E, V)) (k : ℕ) (d e : ℤ) (he : d + k = e)
    (hd : (k : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1) :
    IsIso ((Hfunctor (bundle E hqc).ringCatSheaf
        ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V)
        (m + 1)).map (twistPairingCurry E hqc D k d e he)) := by
  obtain rfl : e = -((m + 1 : ℕ) : ℤ) - 1 := by omega
  let := D.chartData.chart_isOpenImmersion V hV
  have : ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)).IsQuasicoherent :=
    hqc (k : ℤ)
  have : Finite (Monomials m k) := (Finsupp.finite_of_degree_eq k).to_subtype
  rw [← D.chartData.chart_range V hV]
  refine (isIso_hfunctor_image_top_map_iff _ (m + 1) _).mpr ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  have hEv := isIso_biproductLift_sheafHomEval
    ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV)
    ((Scheme.Modules.pullback
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))
    (D.algebra.piece (-((m + 1 : ℕ) : ℤ) - 1))
    (fun α : Monomials m k =>
      chartPullbackSection E hqc D hV k (sectionMonomialBasis E hqc hV b k α))
    fun W hW => by
      have hjW : IsAffineOpen
          (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) ''ᵁ W) :=
        hW.image_of_isOpenImmersion _
      have hle :
          ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV) ''ᵁ W ≤
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V :=
        (((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV).image_mono
          le_top).trans (D.chartData.chart_range V hV).le
      exact bijective_sheafHomEval_pullback _ _ _ _ hV (sectionMonomialBasis E hqc hV b k) _ W
        hjW hle fun α => resImage_chartPullbackSection E hqc D hV k _ W hle
  let H : (AlgebraicGeometry.Proj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)).Modules ⥤ AddCommGrpCat.{u} :=
    Hfunctor (AlgebraicGeometry.Proj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)).ringCatSheaf ⊤ (m + 1)
  have : H.Additive := (inferInstance : (Hfunctor (AlgebraicGeometry.Proj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)).ringCatSheaf ⊤
        (m + 1)).Additive)
  refine bijective_map_of_isIso_biproductLift _ H _
    (biproduct.lift (fun α : Monomials m k => sheafHomEval
      ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV)
      ((Scheme.Modules.pullback
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))
      (D.algebra.piece (-((m + 1 : ℕ) : ℤ) - 1))
      (chartPullbackSection E hqc D hV k (sectionMonomialBasis E hqc hV b k α)))) hEv ?_
  have hmono : ∀ α : Monomials m k,
      (⟨DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces V) k
          (sectionMonomialBasis E hqc hV b k α),
        (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).of_mem_grading V _⟩ :
          (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V k) =
        Stacks.ProjTwistComparison.mapHomogeneous (ofPolyGrading E hqc hV b)
          (monomialElt (A := Γ(S, V)) α) :=
    fun α => Subtype.ext (of_sectionMonomialBasis E hqc hV b α)
  have key : ∀ α : Monomials m k,
      (Scheme.Modules.restrictFunctor
          ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV)).map
          (twistPairingCurry E hqc D k d _ he) ≫
        biproduct.lift (fun α => sheafHomEval
          ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV)
          ((Scheme.Modules.pullback
            (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
            ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))
          (D.algebra.piece (-((m + 1 : ℕ) : ℤ) - 1))
          (chartPullbackSection E hqc D hV k (sectionMonomialBasis E hqc hV b k α))) ≫
        biproduct.π _ α =
      (D.chartData.chartIso V hV d).hom ≫
        twistMulLeftIntOf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)
          (Stacks.ProjTwistComparison.mapHomogeneous (ofPolyGrading E hqc hV b)
            (monomialElt (A := Γ(S, V)) α)) d _ hd ≫
        (D.chartData.chartIso V hV _).inv := by
    intro α
    refine (congrArg (fun g => (Scheme.Modules.restrictFunctor
          ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV)).map
          (twistPairingCurry E hqc D k d _ he) ≫ g)
      (biproduct.lift_π (fun α : Monomials m k => sheafHomEval
        ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hV)
        ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))
        (D.algebra.piece (-((m + 1 : ℕ) : ℤ) - 1))
        (chartPullbackSection E hqc D hV k (sectionMonomialBasis E hqc hV b k α))) α)).trans ?_
    rw [← hmono α]
    exact restrict_twistPairingCurry_sheafHomEval E hqc D hV k d _ he hd _
  have hP := bijective_monomialPairingOf (toPolyGrading E hqc hV b) (ofPolyGrading E hqc hV b)
    (toPolyGrading_ofPolyGrading E hqc hV b) (ofPolyGrading_toPolyGrading E hqc hV b) k d hd
  have hfun := (Function.Bijective.piMap fun _ : Monomials m k =>
      ConcreteCategory.bijective_of_isIso
        (H.mapIso (D.chartData.chartIso V hV (-((m + 1 : ℕ) : ℤ) - 1))).inv).comp
    (hP.comp (ConcreteCategory.bijective_of_isIso (H.mapIso (D.chartData.chartIso V hV d)).hom))
  refine (congrArg Function.Bijective (funext fun c => funext fun α => ?_)).mpr hfun
  rw [key α]
  exact (congrArg (fun f => AddCommGrpCat.Hom.hom f c) ((H.map_comp _ _).trans
    (congrArg (fun g => H.map (D.chartData.chartIso V hV d).hom ≫ g) (H.map_comp _ _)))).trans rfl

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The curried multiplication pairing is an isomorphism on the top higher direct image.**
For `E` finite locally free of constant rank `n + 1`, `n ≥ 1`, and `k + d = -n - 1`,
`Rⁿ π_* 𝒪(d) ⟶ Rⁿ π_* SheafHom(π^* Sym^k(E), 𝒪(-n-1))` is an isomorphism. -/
theorem isIso_rightDerivedPlus_twistPairingCurry {n : ℕ} (hn : 1 ≤ n)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) (k : ℕ) (d e : ℤ)
    (he : d + k = e) (hd : (k : ℤ) + d = -(n : ℤ) - 1) :
    IsIso (((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
      (n : ℤ)).map (twistPairingCurry E hqc D k d e he)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine Stacks.AffineHigherDirectImage.isIso_rightDerivedPlus_pushforward_map_of_isIso_hgroup _ _
    (m + 1) (ProjectiveBundleVanishing.isBasis_trivializing E hfree) fun V hV => ?_
  obtain ⟨b₀⟩ := nonempty_basis_sections E hV.2.some
  exact isIso_hfunctor_preimage_twistPairingCurry E hqc D hV.1 (b₀.reindex Equiv.ulift) k d e he
    (by omega)

end Bundle

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology
